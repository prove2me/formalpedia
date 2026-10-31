-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P55_lemma_3_15
-- name    : QAlgorithms.Papers.Independent.Intake100.P55.lemma_3_15
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:54:59.426306+00:00
-- url     : https://prove2.me/theorems/6439e64f-df5e-406a-a827-9bb3675168da
-- title:
--   Lemma 3.15
-- statement:
--   Let $R$ be a commutative unital ring with units $\lambda,\delta$ and $z\in R$ satisfying $\lambda^{-1}-\lambda=z(\delta-1)$. For the affine algebra specify arbitrary scalars $q_s$ for every positive integer $s$, with no admissibility or cyclotomic condition. Write $W_n$ and $\widehat W_n$ for the ordinary and affine BMW presentations of Definitions 3.1 and 3.6. Lower levels denote their canonical generator images; products of subspaces denote their $R$-linear spans.
--
--   All equalities are in $\widehat W_{n+1}$. For every $n\ge1$ and $s\in\mathbb Z$, there exists $b$ in the canonical image of $\widehat W_{n-1}$ such that
--   $$e_nx_n^se_n=be_n.$$
--   In addition, for every $n\ge2$, $k\ge0$, choices $z_0,\ldots,z_k\in\{e_{n-1},g_{n-1}\}$, and positive integers $r_1,\ldots,r_k$, set $a=z_0x_{n-1}^{r_1}z_1\cdots x_{n-1}^{r_k}z_k$. There exists $b\in\widehat W_{n-1}$ with $e_nae_n=be_n$. Here the $x_j$ are the winding elements of §3.3. These are the two reduction statements used in the affine bimodule description.
-- source:
--   Affine Birman-Wenzl-Murakami Algebras and Tangles in the Solid Torus, arXiv:math/0411155v2, PDF p. 21, Lemma 3.15

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P55

noncomputable section

open scoped Classical

namespace QAlgorithms.Papers.Independent.Intake100.P55

section Statements

variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R)

/-- Lemma 3.15(1),(2), PDF p.21. Lower levels mean canonical images;
the word in (2) has k nonnegative, with all k exponents positive. -/
theorem lemma_3_15 :
    (∀ n, 1 ≤ n → ∀ s : ℤ, ∃ b : OrdinaryAffineBMW P q true (n+1),
      b ∈ bmwLevel P q true true (n+1) (n-1) ∧
      ghContraction P q true (n+1) n * windingPower P q (n+1) n s * ghContraction P q true (n+1) n =
        b * ghContraction P q true (n+1) n) ∧
    (∀ n, 2 ≤ n → ∀ k (zs : Fin (k+1) → OrdinaryAffineBMW P q true (n+1)) (rs : Fin k → ℕ),
      (∀ j, zs j = ghContraction P q true (n+1) (n-1) ∨ zs j = ghCrossing P q true (n+1) (n-1) false) →
      (∀ j, 1 ≤ rs j) → ∃ b : OrdinaryAffineBMW P q true (n+1),
        b ∈ bmwLevel P q true true (n+1) (n-1) ∧
        ghContraction P q true (n+1) n * alternatingWord (bmwWinding P q (n+1) false (n-1)) k zs rs *
          ghContraction P q true (n+1) n = b * ghContraction P q true (n+1) n) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intake100.P55

end
