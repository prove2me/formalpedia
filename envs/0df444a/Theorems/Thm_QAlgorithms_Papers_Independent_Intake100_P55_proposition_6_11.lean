-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P55_proposition_6_11
-- name    : QAlgorithms.Papers.Independent.Intake100.P55.proposition_6_11
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:01:05.370592+00:00
-- url     : https://prove2.me/theorems/a367f210-c790-471f-b5fa-9c15e016d3a0
-- title:
--   Proposition 6.11
-- statement:
--   Let $R$ be a commutative unital ring with units $\lambda,\delta$ and $z\in R$ satisfying $\lambda^{-1}-\lambda=z(\delta-1)$. For the affine algebra specify arbitrary scalars $q_s$ for every positive integer $s$, with no admissibility or cyclotomic condition. Write $W_n$ and $\widehat W_n$ for the ordinary and affine BMW presentations of Definitions 3.1 and 3.6. Lower levels denote their canonical generator images; products of subspaces denote their $R$-linear spans.
--
--   For every $n\ge0$, define $x_j=(g_{j-1}\cdots g_1)x_1(g_1\cdots g_{j-1})$ for $1\le j\le n$. For $\mu\in\mathbb Z^n$, write $x^\mu=x_1^{\mu_1}\cdots x_n^{\mu_n}$. Then
--   $$\widehat W_n=\operatorname{span}_R\{x^\mu w x^\nu:\mu,\nu\in\mathbb Z^n,\ w\in W_n\}.$$
--   The ordinary algebra denotes its canonical generator image. At $n=0$, both Laurent words are empty. This is the unrestricted Laurent-sandwich spanning result preceding the explicit affine bases.
-- source:
--   Affine Birman-Wenzl-Murakami Algebras and Tangles in the Solid Torus, arXiv:math/0411155v2, PDF p. 57, Proposition 6.11

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P55

noncomputable section

open scoped Classical

namespace QAlgorithms.Papers.Independent.Intake100.P55

section Statements

variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R)

/-- Proposition 6.11, PDF p.57. All affine elements are linear combinations
of Laurent sandwiches of elements in the ordinary canonical image. -/
theorem proposition_6_11 (n : ℕ) :
    Submodule.span R {a : OrdinaryAffineBMW P q true n | ∃ (mu nu : Fin n → ℤ)
      (w : OrdinaryAffineBMW P q true n), w ∈ bmwLevel P q true false n n ∧
      a = laurent P q n mu * w * laurent P q n nu} = ⊤ := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intake100.P55

end
