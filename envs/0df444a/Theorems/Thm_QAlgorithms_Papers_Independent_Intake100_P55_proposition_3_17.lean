-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P55_proposition_3_17
-- name    : QAlgorithms.Papers.Independent.Intake100.P55.proposition_3_17
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:56:00.052774+00:00
-- url     : https://prove2.me/theorems/d08b85d9-2d52-4632-8de9-54cadf8bdff6
-- title:
--   Proposition 3.17
-- statement:
--   Let $R$ be a commutative unital ring with units $\lambda,\delta$ and $z\in R$ satisfying $\lambda^{-1}-\lambda=z(\delta-1)$. For the affine algebra specify arbitrary scalars $q_s$ for every positive integer $s$, with no admissibility or cyclotomic condition. Write $W_n$ and $\widehat W_n$ for the ordinary and affine BMW presentations of Definitions 3.1 and 3.6. Lower levels denote their canonical generator images; products of subspaces denote their $R$-linear spans.
--
--   For every $n\ge1$, inside $\widehat W_{n+1}$,
--   $$e_n\widehat W_ne_n=\widehat W_{n-1}e_n.$$
--   Both sides mean linear spans using the canonical lower-level images. The equality is the full printed result, including its immediate reverse containment. It describes the affine contraction corner.
-- source:
--   Affine Birman-Wenzl-Murakami Algebras and Tangles in the Solid Torus, arXiv:math/0411155v2, PDF p. 25, Proposition 3.17

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P55

noncomputable section

open scoped Classical

namespace QAlgorithms.Papers.Independent.Intake100.P55

section Statements

variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R)

/-- Proposition 3.17, PDF p.25. The source states equality, including the
reverse containment which its proof calls immediate. -/
theorem proposition_3_17 (n : ℕ) (hn : 1 ≤ n) :
    bmwCornerSpan (R := R) (ghContraction P q true (n+1) n)
      (bmwLevel P q true true (n+1) n : Set (OrdinaryAffineBMW P q true (n+1))) =
    rightSpan (R := R) (bmwLevel P q true true (n+1) (n-1) : Set (OrdinaryAffineBMW P q true (n+1)))
      (ghContraction P q true (n+1) n) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intake100.P55

end
