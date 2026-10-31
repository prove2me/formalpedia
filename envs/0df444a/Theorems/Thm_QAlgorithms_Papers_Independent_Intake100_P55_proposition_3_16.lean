-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P55_proposition_3_16
-- name    : QAlgorithms.Papers.Independent.Intake100.P55.proposition_3_16
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:55:34.616014+00:00
-- url     : https://prove2.me/theorems/1dd468c8-a34b-44a6-8ea8-6749e2ada2ae
-- title:
--   Proposition 3.16
-- statement:
--   Let $R$ be a commutative unital ring with units $\lambda,\delta$ and $z\in R$ satisfying $\lambda^{-1}-\lambda=z(\delta-1)$. For the affine algebra specify arbitrary scalars $q_s$ for every positive integer $s$, with no admissibility or cyclotomic condition. Write $W_n$ and $\widehat W_n$ for the ordinary and affine BMW presentations of Definitions 3.1 and 3.6. Lower levels denote their canonical generator images; products of subspaces denote their $R$-linear spans.
--
--   For every $n\ge2$, put $C_n=\{e_{n-1},g_{n-1}^{\pm1}\}\cup\{x_n^r:r\in\mathbb Z\}$, where $x_n$ is the winding element of §3.3. Set $C_1=\{x_1^r:r\in\mathbb Z\}$. Then
--   $$\widehat W_n=\operatorname{span}_R\{a\chi b:a,b\in\widehat W_{n-1},\ \chi\in C_n\}\qquad(n\ge1).$$
--   In particular the first level is the Laurent span. This is the affine tower's bimodule spanning result.
-- source:
--   Affine Birman-Wenzl-Murakami Algebras and Tangles in the Solid Torus, arXiv:math/0411155v2, PDF p. 23, Proposition 3.16

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P55

noncomputable section

open scoped Classical

namespace QAlgorithms.Papers.Independent.Intake100.P55

section Statements

variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R)

/-- Proposition 3.16, PDF pp.23--24. At n=1 only Laurent powers of x_1
are inserted, as in the source's base case; no g_0 or e_0 is used. -/
theorem proposition_3_16 (n : ℕ) (hn : 1 ≤ n) :
    insertionSpan (R := R) (bmwLevel P q true true n (n-1) : Set (OrdinaryAffineBMW P q true n))
      {chi | (∃ r : ℤ, chi = windingPower P q n n r) ∨
        (2 ≤ n ∧ (chi = ghContraction P q true n (n-1) ∨
          chi = ghCrossing P q true n (n-1) false ∨ chi = ghCrossing P q true n (n-1) true))} = ⊤ := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intake100.P55

end
