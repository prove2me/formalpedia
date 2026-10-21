-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P04_sl2_H2_embedding
-- name    : QAlgorithms.Papers.Independent.Claimed50.P04.sl2_H2_embedding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:39:49.162666+00:00
-- url     : https://prove2.me/theorems/5a0f2d1a-0255-4b39-8e55-63470f183c55
-- title:
--   Lemma 2.7
-- statement:
--   Let $\mathfrak g$ be a finite-dimensional real hermitian simple Lie algebra of tube type, $H_0$ an H-element, and $0\ne h\in[H_0,\mathfrak g]$ with the three eigenspaces of $\operatorname{ad}h$ spanning $\mathfrak g$. Put $H=\operatorname{diag}(1,-1)$ and $U=\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$. There is a real Lie algebra homomorphism $\kappa:\mathfrak{sl}_2(\mathbb R)\to\mathfrak g$ such that
--   $$\kappa(U/2)=H_0,\qquad \kappa(H/2)=h.$$
--   The first identity is the H2 compatibility. This embeds the standard grading model with the specified normalization.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, PDF p. 6, Lemma 2.7

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

/-- Lemma 2.7, PDF p. 6. The homomorphism is H2: kappa(U/2)=H0, and sends H/2
to the given nonzero h in [H0,g]. No orbit-chosen h replaces the given element. -/
theorem sl2_H2_embedding {G : Type*} [LieRing G] [LieAlgebra ℝ G]
    [FiniteDimensional ℝ G] [LieAlgebra.IsSimple ℝ G]
    (hh : Hermitian (G := G)) (ht : TubeType (G := G))
    (H0 h : G) (hH : HElement H0)
    (hin : h ∈ (LieAlgebra.ad ℝ G H0).range) (hne : h ≠ 0)
    (hg : ThreeGraded (LieAlgebra.ad ℝ G h)) :
    ∃ kappa : LieAlgebra.SpecialLinear.sl (Fin 2) ℝ →ₗ⁅ℝ⁆ G,
      kappa ((1 / 2 : ℝ) • sl2U) = H0 ∧ kappa ((1 / 2 : ℝ) • sl2H) = h := by sorry

end

end QAlgorithms.Papers.Independent.Claimed50.P04
