-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P55_corollary_3_18
-- name    : QAlgorithms.Papers.Independent.Intake100.P55.corollary_3_18
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:56:36.723425+00:00
-- url     : https://prove2.me/theorems/78ebc56c-c9f2-4d54-b48b-cd5f8505a03b
-- title:
--   Corollary 3.18
-- statement:
--   Let $R$ be a commutative unital ring with units $\lambda,\delta$ and $z\in R$ satisfying $\lambda^{-1}-\lambda=z(\delta-1)$. For the affine algebra specify arbitrary scalars $q_s$ for every positive integer $s$, with no admissibility or cyclotomic condition. Write $W_n$ and $\widehat W_n$ for the ordinary and affine BMW presentations of Definitions 3.1 and 3.6. Lower levels denote their canonical generator images; products of subspaces denote their $R$-linear spans.
--
--   For every $n\ge1$, inside the ordinary algebra $W_{n+1}$,
--   $$e_nW_ne_n=W_{n-1}e_n.$$
--   Both sides mean linear spans of the indicated products. This is the ordinary contraction-corner identity.
-- source:
--   Affine Birman-Wenzl-Murakami Algebras and Tangles in the Solid Torus, arXiv:math/0411155v2, PDF p. 25, Corollary 3.18

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P55

noncomputable section

open scoped Classical

namespace QAlgorithms.Papers.Independent.Intake100.P55

section Statements

variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R)

/-- Corollary 3.18, PDF p.25. Products denote linear spans in W_(n+1). -/
theorem corollary_3_18 (n : ℕ) (hn : 1 ≤ n) :
    bmwCornerSpan (R := R) (ghContraction P q false (n+1) n)
      (bmwLevel P q false false (n+1) n : Set (OrdinaryAffineBMW P q false (n+1))) =
    rightSpan (R := R) (bmwLevel P q false false (n+1) (n-1) : Set (OrdinaryAffineBMW P q false (n+1)))
      (ghContraction P q false (n+1) n) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intake100.P55

end
