-- Prove2me | Theorems.Thm_StochSchedPrec_InForest_lemma_3_3
-- name    : StochSchedPrec.InForest.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:44:12.141063+00:00
-- url     : https://prove2.me/theorems/3e6a5d14-26ad-47bd-8050-70ab4e39ec74
-- title:
--   Lemma 3.3, p. 797 — (1/m) Σ_{k≤j} E[P_k] ≤ (1 + max{1, (m−1)Δ/m}) C^LP_j
-- statement:
--   Let $m\ge1$, $\Delta\ge0$, and let $\mu_j>0$ ($j\in V$) be the expected processing times. Let $C\in\mathbb R^V$ satisfy the first and the last set of inequalities of the LP-relaxation,
--   $$\sum_{j\in W}\mu_jC_j\ge f(W)\quad(W\subseteq V),\qquad C_j\ge\mu_j\quad(j\in V),$$
--   and let $L$ be a priority list along which $C$ is nondecreasing. Then for every job $j$, with $B_j$ the jobs up to and including $j$ in $L$,
--   $$\frac1m\sum_{k\in B_j}\mu_k\ \le\ \Big(1+\max\Big\{1,\frac{m-1}{m}\Delta\Big\}\Big)\,C_j .$$
--
--   The lemma converts the LP solution into a bound on the total expected work ahead of each job in the list, which is the second term in Lemma 4.4.
--
--   **Formalization Note** The page writes the jobs as $1,\dots,n$ with $C_1\le\dots\le C_n$ and sums over $k=1,\dots,j$; here this is the prefix $B_j$ of a list sorted by $C$.
-- source:
--   Skutella and Uetz, Stochastic machine scheduling with precedence constraints, SIAM J. Comput. 34(4) (2005) 788–802, p. 797, Lemma 3.3 (see [15, Lemma 4.2])

import Mathlib
import Definitions.Def_StochSchedPrec_InForest_LP

namespace StochSchedPrec.InForest

theorem lemma_3_3 {V : Type*} [Fintype V] [DecidableEq V]
    (m : ℕ) (hm : 0 < m) (Δ : ℝ) (hΔ : 0 ≤ Δ) (μ : V → ℝ) (hμ : ∀ j, 0 < μ j)
    (C : V → ℝ) (hload : ∀ W : Finset V, f μ m Δ W ≤ ∑ j ∈ W, μ j * C j)
    (hlow : ∀ j, μ j ≤ C j)
    (L : Fin (Fintype.card V) ≃ V) (hL : StochSchedPrec.CMNS.IsSortedBy L C) (j : V) :
    1 / (m : ℝ) * ∑ k ∈ Bset L j, μ k ≤ (1 + max 1 (((m : ℝ) - 1) / m * Δ)) * C j := by sorry

end StochSchedPrec.InForest
