-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P55_lemma_3_19
-- name    : QAlgorithms.Papers.Independent.Intake100.P55.lemma_3_19
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:57:11.610994+00:00
-- url     : https://prove2.me/theorems/203a3ebf-2c2c-4cf6-afa2-abc9a75ca527
-- title:
--   Lemma 3.19
-- statement:
--   Let $R$ be a commutative unital ring with units $\lambda,\delta$ and $z\in R$ satisfying $\lambda^{-1}-\lambda=z(\delta-1)$. For the affine algebra specify arbitrary scalars $q_s$ for every positive integer $s$, with no admissibility or cyclotomic condition. Write $W_n$ and $\widehat W_n$ for the ordinary and affine BMW presentations of Definitions 3.1 and 3.6. Lower levels denote their canonical generator images; products of subspaces denote their $R$-linear spans.
--
--   For every $n\ge1$ and $r\in\mathbb Z$, inside $\widehat W_{n+1}$,
--   $$g_n^{\pm1}\widehat W_ne_n\subseteq\widehat W_ne_n,\qquad x_{n+1}^r\widehat W_ne_n\subseteq\widehat W_ne_n.$$
--   The winding element $x_{n+1}$ is the word from §3.3 and all products denote linear spans. Thus these additional affine generators preserve the indicated submodule.
-- source:
--   Affine Birman-Wenzl-Murakami Algebras and Tangles in the Solid Torus, arXiv:math/0411155v2, PDF p. 25, Lemma 3.19

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P55

noncomputable section

open scoped Classical

namespace QAlgorithms.Papers.Independent.Intake100.P55

section Statements

variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R)

/-- Lemma 3.19, PDF p.25. Both g_n signs and every integer bmwWinding
power x_(n+1)^r preserve the indicated right-product submodule. -/
theorem lemma_3_19 (n : ℕ) (hn : 1 ≤ n) :
    let V := rightSpan (R := R)
      (bmwLevel P q true true (n+1) n : Set (OrdinaryAffineBMW P q true (n+1))) (ghContraction P q true (n+1) n)
    (∀ inv : Bool, translateSpan (ghCrossing P q true (n+1) n inv) V ≤ V) ∧
    (∀ r : ℤ, translateSpan (windingPower P q (n+1) (n+1) r) V ≤ V) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intake100.P55

end
