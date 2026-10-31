-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P55_proposition_3_20
-- name    : QAlgorithms.Papers.Independent.Intake100.P55.proposition_3_20
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:57:37.617963+00:00
-- url     : https://prove2.me/theorems/b573d9f0-3534-44ed-9f26-1ee3b3b157cc
-- title:
--   Proposition 3.20
-- statement:
--   Let $R$ be a commutative unital ring with units $\lambda,\delta$ and $z\in R$ satisfying $\lambda^{-1}-\lambda=z(\delta-1)$. For the affine algebra specify arbitrary scalars $q_s$ for every positive integer $s$, with no admissibility or cyclotomic condition. Write $W_n$ and $\widehat W_n$ for the ordinary and affine BMW presentations of Definitions 3.1 and 3.6. Lower levels denote their canonical generator images; products of subspaces denote their $R$-linear spans.
--
--   For every $n\ge1$, inside $\widehat W_{n+1}$,
--   $$\widehat W_{n+1}e_n=\widehat W_ne_n.$$
--   Here the smaller algebra means its canonical generator image and products denote linear spans. The right ideal already comes from the preceding level.
-- source:
--   Affine Birman-Wenzl-Murakami Algebras and Tangles in the Solid Torus, arXiv:math/0411155v2, PDF p. 25, Proposition 3.20

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P55

noncomputable section

open scoped Classical

namespace QAlgorithms.Papers.Independent.Intake100.P55

section Statements

variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R)

/-- Proposition 3.20, PDF p.25, with explicit ambient algebra W_(n+1). -/
theorem proposition_3_20 (n : ℕ) (hn : 1 ≤ n) :
    rightSpan (R := R) (Set.univ : Set (OrdinaryAffineBMW P q true (n+1))) (ghContraction P q true (n+1) n) =
    rightSpan (R := R) (bmwLevel P q true true (n+1) n : Set (OrdinaryAffineBMW P q true (n+1)))
      (ghContraction P q true (n+1) n) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intake100.P55

end
