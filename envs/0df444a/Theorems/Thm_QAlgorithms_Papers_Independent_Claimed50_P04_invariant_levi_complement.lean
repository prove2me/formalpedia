-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P04_invariant_levi_complement
-- name    : QAlgorithms.Papers.Independent.Claimed50.P04.invariant_levi_complement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:47:08.190642+00:00
-- url     : https://prove2.me/theorems/edfa783d-ffa8-4263-9e96-bb41c018c081
-- title:
--   Lemma 2.26
-- statement:
--   Let $\mathfrak g$ be a finite-dimensional Lie algebra over $\mathbb R$ or $\mathbb C$, and let $D$ be a derivation whose three actual eigenspaces at $-1,0,1$ span $\mathfrak g$. There is a semisimple subalgebra $\mathfrak s$ with
--   $$\mathfrak g=\operatorname{rad}(\mathfrak g)\rtimes\mathfrak s,\qquad D(\mathfrak s)\subseteq\mathfrak s.$$
--   No admissibility or nonzero assumption is made. This is the derivation-invariant Levi complement.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, PDF p. 13, Lemma 2.26

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

section Levi

variable {K G : Type*} [RCLike K] [LieRing G] [LieAlgebra K G] [FiniteDimensional K G]

/-- Lemma 2.26, PDF p. 13, over R AND C. No admissibility assumption. -/
theorem invariant_levi_complement (D : LieDerivation K G G)
    (hd : ThreeGraded D.toLinearMap) :
    ∃ S : LieSubalgebra K G, InvariantLevi D S := by sorry

end Levi

end

end QAlgorithms.Papers.Independent.Claimed50.P04
