-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P55_proposition_3_14
-- name    : QAlgorithms.Papers.Independent.Intake100.P55.proposition_3_14
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:54:22.902979+00:00
-- url     : https://prove2.me/theorems/314cbc0e-7a11-4f39-9f4b-e968b51f6857
-- title:
--   Proposition 3.14
-- statement:
--   Let $R$ be a commutative unital ring with units $\lambda,\delta$ and $z\in R$ satisfying $\lambda^{-1}-\lambda=z(\delta-1)$. For the affine algebra specify arbitrary scalars $q_s$ for every positive integer $s$, with no admissibility or cyclotomic condition. Write $W_n$ and $\widehat W_n$ for the ordinary and affine BMW presentations of Definitions 3.1 and 3.6. Lower levels denote their canonical generator images; products of subspaces denote their $R$-linear spans.
--
--   For $n\ge2$, the ordinary algebra is spanned by the elements $a\chi b$ with $a,b$ in the canonical image of $W_{n-1}$ and $\chi\in\{1,e_{n-1},g_{n-1},g_{n-1}^{-1}\}$:
--   $$W_n=\operatorname{span}_R\{a\chi b:a,b\in W_{n-1},\ \chi\in\{1,e_{n-1},g_{n-1}^{\pm1}\}\}.$$
--   At $n=1$, the same formula uses only $\chi=1$, since $W_0=W_1=R$. This describes the ordinary tower as a bimodule.
-- source:
--   Affine Birman-Wenzl-Murakami Algebras and Tangles in the Solid Torus, arXiv:math/0411155v2, PDF p. 21, Proposition 3.14

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P55

noncomputable section

open scoped Classical

namespace QAlgorithms.Papers.Independent.Intake100.P55

section Statements

variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R)

/-- Proposition 3.14, PDF p.21. The n=1 case has insertion set {1};
the g/e insertions are present only for n≥2. -/
theorem proposition_3_14 (n : ℕ) (hn : 1 ≤ n) :
    insertionSpan (R := R) (bmwLevel P q false false n (n-1) : Set (OrdinaryAffineBMW P q false n))
      {chi | chi = 1 ∨ (2 ≤ n ∧ (chi = ghContraction P q false n (n-1) ∨
        chi = ghCrossing P q false n (n-1) false ∨ chi = ghCrossing P q false n (n-1) true))} = ⊤ := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intake100.P55

end
