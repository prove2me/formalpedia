-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_neighpr_wit
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.neighpr_wit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:52:16.272011+00:00
-- url     : https://prove2.me/theorems/e93e3056-43ae-4866-8001-28c0d6cd1398
-- title:
--   §4.2, Lemma neighpr_wit
-- statement:
--   Let $R$ be a discrete ordered field equipped with a witness-returning intermediate value operation for polynomials. No completeness or Archimedean hypothesis is imposed. Let $N_+(P,x,b)=(x,n(P,x,b))$ be the right neighborhood ending at the next root, with the specified total defaults. If $x<b$ and $P\ne0$, then
--
--   $$\exists y\in R,\quad y\in N_+(P,x,b).$$
--
--   Both hypotheses ensure that this open neighborhood has a witness.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 20, §4.2, Lemma neighpr_wit

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF p. 20, neighpr_wit, with both nondegeneracy hypotheses. -/
theorem neighpr_wit {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (p : Polynomial R) (x b : R) (hxb : x < b) (hp : p ≠ 0) :
    ∃ y : R, y ∈ neighpr p x b := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
