-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P04_generalized_symplectic_centralizer
-- name    : QAlgorithms.Papers.Independent.Claimed50.P04.generalized_symplectic_centralizer
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:54:27.297172+00:00
-- url     : https://prove2.me/theorems/af0880cb-2fd9-48e7-bc32-a423af399976
-- title:
--   Remark 2.21: generalized symplectic centralizer
-- statement:
--   Let $V,Z$ be finite-dimensional real spaces and $\beta:V\times V\to Z$ alternating bilinear. Suppose $\Omega=f\circ\beta$ is symplectic. For each $g\in Z^*$ there is a unique linear map $\Psi_g$ satisfying $g(\beta(v,w))=\Omega(\Psi_gv,w)$. Each $\Psi_g$ is $\Omega$-symmetric and commutes with $\mathfrak{sp}(V,\beta)$. For every generating subset $S\subseteq Z^*$,
--   $$\mathfrak{sp}(V,\beta)=\{X\in\mathfrak{sp}(V,\Omega):[X,\Psi_g]=0\text{ for all }g\in S\}.$$
--   The operators are existential conclusions with a uniqueness equation. This describes generalized symplectic endomorphisms as a simultaneous centralizer.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, PDF p. 11, Remark 2.21: generalized symplectic centralizer

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

/-- Remark 2.21, PDF p. 11: unique scalar-form operators, their symmetry, full
commutation, and equality of generalized sp with the simultaneous centralizer. -/
theorem generalized_symplectic_centralizer
    (b : V →ₗ[ℝ] V →ₗ[ℝ] Z) (halt : ∀ v, b v v = 0)
    (f : Z →ₗ[ℝ] ℝ) (hs : Symplectic (scalarize b f)) :
    ∃ psi : (Z →ₗ[ℝ] ℝ) → Module.End ℝ V,
      (∀ g : Z →ₗ[ℝ] ℝ, ∀ T : Module.End ℝ V,
        (∀ v w, g (b v w) = scalarize b f (T v) w) ↔ T = psi g) ∧
      (∀ g, AdjointPair (scalarize b f) (psi g) (psi g)) ∧
      (∀ g, ∀ X : Module.End ℝ V, PreservesForm b X →
        (psi g).comp X = X.comp (psi g)) ∧
      (∀ S : Set (Z →ₗ[ℝ] ℝ), Submodule.span ℝ S = ⊤ →
        ∀ X : Module.End ℝ V, PreservesForm b X ↔
          PreservesForm (scalarize b f) X ∧
            ∀ g ∈ S, X.comp (psi g) = (psi g).comp X) := by sorry

end Heisenberg

end

end QAlgorithms.Papers.Independent.Claimed50.P04
