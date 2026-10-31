-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P38_permutation_center
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P38.permutation_center
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:39:45.292994+00:00
-- url     : https://prove2.me/theorems/f7ac9a6e-f431-491c-b585-70f0c70af06a
-- title:
--   Lemma 2: center of the permutation image
-- statement:
--   Let $T_\mu$ consist of permutations with exactly $\mu$ disjoint transpositions and all other points fixed, and let $L_\mu=\sum_{\pi\in T_\mu}R(\pi)$, where $R(\pi)|b\rangle=|b\circ\pi^{-1}\rangle$.
--   Let $\mathcal A_n=\operatorname{span}_{\mathbb C}\{R(\pi):\pi\in S_n\}$ be the complex group-algebra image, and let $\mathfrak p_n=\{A\in\mathcal A_n:A^\dagger=-A\}$. For every $n\ge0$,
--   $$\mathfrak z(\mathfrak p_n)=\operatorname{span}_{\mathbb R}\{iL_\mu:0\le2\mu\le n\}.$$
--
--   The skew part of the complex image corrects (B3): arbitrary permutation matrices need not be Hermitian. The source cites an alternative proof in Ref. [56] and notes overlap with Ref. [18].
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, PDF p. 12, lemma2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF pp.12–13, Lemma 2: center of the skew part of the complex permutation
image. Corrects (B3), which incorrectly spans iR(pi) over R for arbitrary pi.
Alternative proof is cited to Ref.[56]; p.13 also credits Ref.[18]. -/
theorem permutation_center (n : ℕ) :
    algebraCenter (permutationImage n) =
      Submodule.span ℝ {A | ∃ mu : ℕ, 2 * mu ≤ n ∧
        A = Complex.I • transpositionSum n mu} := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P38

end
