/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, Robin Gieseke
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Topology.VectorBundle.Constructions

/-!
# Trivial connection on the trivial bundle

The manifold derivative defines a covariant derivative on the trivial bundle `Trivial M F`.

## Main results

* `Bundle.Trivialization.mdifferentiableAt_section_trivial_iff`: for the trivial bundle,
  mdifferentiability of a section is equivalent to mdifferentiability of the underlying function.
* `IsCovariantDerivativeOn.trivial`: the manifold derivative is a covariant derivative
  on `Set.univ` for the trivial bundle.
* `CovariantDerivative.trivial`: bundled version.
-/

open Bundle NormedSpace
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]

@[expose] public noncomputable section

@[simp]
lemma Bundle.Trivialization.mdifferentiableAt_section_trivial_iff
    {σ : (x : M) → Trivial M F x} {x : M} :
    MDiffAt (T% σ) x ↔ MDifferentiableAt I 𝓘(𝕜, F) (fun b ↦ σ b) x := by
  simp [mdifferentiableAt_section, trivializationAt, Trivial.fiberBundle_trivializationAt']

variable {F}

/-- The manifold derivative is a covariant derivative on `Set.univ` for the trivial bundle. -/
theorem IsCovariantDerivativeOn.trivial :
    IsCovariantDerivativeOn F
      (fun (σ : Π x : M, Trivial M F x) (x : M) ↦ mfderiv I 𝓘(𝕜, F) σ x)
      Set.univ where
  add hσ hσ' _ := by
    simp only [Trivialization.mdifferentiableAt_section_trivial_iff] at hσ hσ'
    exact mfderiv_add hσ hσ'
  leibniz hσ hg _ := by
    simp only [Trivialization.mdifferentiableAt_section_trivial_iff] at hσ
    ext v; exact fromTangentSpace_mfderiv_smul_apply hg hσ v

/-- The trivial connection on the trivial bundle `Trivial M F`. -/
def CovariantDerivative.trivial : CovariantDerivative I F (Bundle.Trivial M F) where
  toFun σ x := mfderiv I 𝓘(𝕜, F) σ x
  isCovariantDerivativeOnUniv := IsCovariantDerivativeOn.trivial

end
