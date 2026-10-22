-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_sgp_right_scale
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.sgp_right_scale
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:43:11.827977+00:00
-- url     : https://prove2.me/theorems/28b25e0d-0ddb-4489-a46c-4d0064f630a9
-- title:
--   §3.2, Lemma sgp_right_scale
-- statement:
--   Let $R$ be a discrete totally ordered integral domain, with order compatible with its ring operations. For $c,x\in R$ and $P\in R[X]$, let $\operatorname{sgn}$ take values in $\mathbb Z$, and let $s_+(P,x)$ be the sign of the first nonzero evaluation at $x$ among $P,P',P'',\ldots$, with value zero if all vanish. Then
--
--   $$s_+(cP,x)=\operatorname{sgn}(c)s_+(P,x).$$
--
--   This describes scalar multiplication of the right sign.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 12, §3.2, Lemma sgp_right_scale

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF p. 12, sgp_right_scale; ordered integral domains suffice. -/
theorem sgp_right_scale {R : Type*} [CommRing R] [IsDomain R]
    [LinearOrder R] [IsStrictOrderedRing R] (c : R) (p : Polynomial R) (x : R) :
    rightSign (c • p) x = sgr c * rightSign p x := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
