-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P05_proposition_3_19
-- name    : QAlgorithms.Papers.Independent.Next46.P05.proposition_3_19
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:03:46.086457+00:00
-- url     : https://prove2.me/theorems/d1cd848a-a1f2-4cac-921e-7fa1411757cc
-- title:
--   Proposition 3.19: a common paired Cartan basis and bracket containment
-- statement:
--   All Lie algebras below are real and finite-dimensional, with their usual Hausdorff vector-space topology; brackets of subspaces denote real linear spans. Let $\mathfrak g$ be hermitian simple. Write $W_{\min}$ for a chosen minimal pointed generating invariant closed convex cone, with its orientation fixed. Let $\tau$ be an involutive Lie automorphism reversing $W_{\min}$, and $\theta$ a commuting Cartan involution. Put $\mathfrak p=\mathfrak g^{-\theta}$ and $r=\operatorname{rank}_{\mathbb R}\mathfrak g$. There exists a $\tau$-stable maximal abelian $\mathfrak a\subseteq\mathfrak p$ such that, with $\mathfrak a_h=\mathfrak a\cap\mathfrak g^\tau$, either $\mathfrak a_h=\mathfrak a$, or $r=2s$ and $\mathfrak a$ has a basis $H_1,\ldots,H_{2s}$ with $\tau H_\ell=H_{\ell+s}$, whose pair-sums $K_\ell=H_\ell+H_{\ell+s}$ form a basis of $\mathfrak a_h$. Relative to the dual basis, the restricted roots are exactly $C_r$ in tube type and $BC_r$ otherwise, with their root sets as in (4),(5).
--
--   After this common choice of $\mathfrak a$, every $h_0\in\mathfrak a_h$ with adjoint spectrum contained in $\{0,\pm\frac12,\pm1\}$ and $\operatorname{rank}_{\mathbb R}\mathfrak g_t(h_0)=r$ satisfies
--
--   $$\mathfrak a_h\subseteq[\mathfrak g^{-\tau}_{-1}(h_0),\mathfrak g^{-\tau}_1(h_0)].$$
--
--   The subspace and basis precede the universal choice of $h_0$. This is a structural statement used in the paper's classification of causal subalgebras.
-- source:
--   Classification of 3-graded causal subalgebras of real simple Lie algebras, arXiv:2001.03125v2, PDF p. 27, Proposition 3.19

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P05

namespace QAlgorithms.Papers.Independent.Next46.P05

noncomputable section

open Set

open QAlgorithms.Papers.Independent.Frontier30.P26
  (bracketSpan innerWord Invariant ClosedCone GeneratingInvariantCone CompactlyEmbedded)

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P05.lieNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P05.lieNormedSpace

section FinalStatements

variable {G : Type*} [LieRing G] [LieAlgebra ℝ G] [FiniteDimensional ℝ G]

/-- Proposition 3.19(a),(b), PDF pp. 27–28. A and the normalized basis are chosen
simultaneously before the universal h0. Both paired-basis assertions and both root types remain. -/
theorem proposition_3_19 (hg : HermitianSimple (G := G)) (Wmin : Set G)
    (hm : MinimalCone Wmin) (tau theta : G ≃ₗ⁅ℝ⁆ G) (hp : CompatiblePair Wmin tau theta) :
    ∃ A : Submodule ℝ G,
      tau '' (A : Set G) = (A : Set G) ∧ MaximalAbelianIn A (autoSpace theta (-1)) ∧
      ((A ⊓ autoSpace tau 1 = A) ∨
        ∃ s : ℕ, realRank (G := G) = 2 * s ∧
          ∃ b : Module.Basis (Fin (2 * s)) ℝ A,
            (∀ l : Fin s,
              tau (b ⟨l.val, by omega⟩ : G) = (b ⟨l.val + s, by omega⟩ : G)) ∧
            (∃ k : Module.Basis (Fin s) ℝ ↥(A ⊓ autoSpace tau 1),
              ∀ l : Fin s, (k l : G) =
                (b ⟨l.val, by omega⟩ : G) + (b ⟨l.val + s, by omega⟩ : G)) ∧
            (RestrictedTubeType (G := G) → {a | RestrictedRoot A a} = rootsC b) ∧
            (¬ RestrictedTubeType (G := G) → {a | RestrictedRoot A a} = rootsBC b)) ∧
      ∀ h0 : G, h0 ∈ A ⊓ autoSpace tau 1 →
        complexSpectrum (LieAlgebra.ad ℝ G h0) ⊆ fiveSpectrum →
        realRank (G := tubeAlgebra h0) = realRank (G := G) →
        A ⊓ autoSpace tau 1 ≤ bracketSpan (adSpace h0 (-1) ⊓ autoSpace tau (-1))
          (adSpace h0 1 ⊓ autoSpace tau (-1)) := by sorry

end FinalStatements

end

end QAlgorithms.Papers.Independent.Next46.P05
