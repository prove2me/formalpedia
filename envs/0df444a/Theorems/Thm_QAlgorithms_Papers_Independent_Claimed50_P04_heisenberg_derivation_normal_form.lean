-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P04_heisenberg_derivation_normal_form
-- name    : QAlgorithms.Papers.Independent.Claimed50.P04.heisenberg_derivation_normal_form
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:56:54.685866+00:00
-- url     : https://prove2.me/theorems/893731d6-e14e-4d60-8465-3cd170e03c22
-- title:
--   Example 3.5: Heisenberg derivation normal form
-- statement:
--   Let $(V,\Omega)$ be a finite-dimensional real symplectic vector space, including $V=0$, and give $V\oplus\mathbb R$ its Heisenberg bracket. Every derivation $D$ has $c\in\mathbb R$, $A\in\mathfrak{sp}(V,\Omega)$, and $w\in V$ with
--   $$D(v,z)=\bigl(\tfrac c2v+Av,\;cz+\Omega(w,v)\bigr).$$
--   The map $D_c(v,z)=(cv/2,cz)$ is a derivation and equals $D$ on the center. Thus $D-D_c$ vanishes there, with vector block $A$ and central block $\Omega(w,\cdot)$. This fixes the source's center-scaling normalization.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, PDF p. 17, Example 3.5: Heisenberg derivation normal form

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P04

namespace QAlgorithms.Papers.Independent.Claimed50.P04

noncomputable section

open Set

attribute [local instance 100] LieRing.ofAssociativeRing

open QAlgorithms.Papers.Independent.Frontier30.P26
  (Invariant LieAdmissible ClosedCone CompactlyEmbedded CompactCartan Hermitian bracketSpan
    TubeType)

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P04.lieNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P04.lieNormedSpace

section Heisenberg

variable {V Z : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup Z] [Module ℝ Z] [FiniteDimensional ℝ Z]

/-- Example 3.5, PDF p. 17. The center scaling c has vector scaling c/2,
unlike the conformal-Jacobi parameter c,2c. The remaining central block is omega(w,-). -/
theorem heisenberg_derivation_normal_form
    (omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hs : Symplectic omega)
    (D : Module.End ℝ (V × ℝ)) (hd : HeisenbergDerivation omega D) :
    ∃ c : ℝ, ∃ A : Module.End ℝ V, ∃ w : V,
      PreservesForm omega A ∧
      (∀ v z, D (v, z) = ((c / 2) • v + A v, c * z + omega w v)) ∧
      HeisenbergDerivation omega (diagonalBlocks ((c / 2) • LinearMap.id) (c • LinearMap.id)) ∧
      (∀ z, D (0, z) = (0, c * z)) := by sorry

end Heisenberg

end

end QAlgorithms.Papers.Independent.Claimed50.P04
