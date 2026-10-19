-- Prove2me | Theorems.Thm_PromoMulti_PairwiseExact_pairwise_sum_higher_zero
-- name    : PromoMulti.PairwiseExact.pairwise_sum_higher_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:19.757097+00:00
-- url     : https://prove2.me/theorems/064e6ddb-3875-4866-b867-ed1f357a063c
-- title:
--   §3, remark after Theorem 1, p. 14 — for a binary objective that is a sum of functions of at most two variables, all coefficients of order ≥ 3 vanish
-- statement:
--   Let $x\in\{0,1\}^n$ be a vector of binary decision variables and let the objective be a finite sum $f(x)=\sum_{r=1}^m g_r(x)$, where each $g_r$ depends only on the coordinates in a set $A_r\subseteq\{1,\dots,n\}$ with $|A_r|\le 2$. For a set $U$ write $\mathbf 1_U$ for its indicator vector. Then for every set $S$ of at least three variables,
--   $$\sum_{U\subseteq S}(-1)^{|S|-|U|}\,f(\mathbf 1_U)=0.$$
--
--   In words, the coefficients of order three and higher of the inclusion–exclusion (pseudo-Boolean) expansion of such an objective are zero, so the pairwise approximation captures it exactly. The paper notes that the conclusion of Theorem 1 extends in this way to a general binary nonlinear IP.
--
--   **Formalization Note.** "Depends only on the coordinates in $A_r$" means $g_r(x)=g_r(y)$ whenever $x$ and $y$ agree on $A_r$.
-- source:
--   Cohen, Kalas & Perakis, Promotion Optimization for Multiple Items in Supermarkets, SSRN preprint 3061451, p. 14 (PDF 14), §3, paragraph after Theorem 1

import Mathlib

namespace PromoMulti.PairwiseExact

theorem pairwise_sum_higher_zero {n m : ℕ} (A : Fin m → Finset (Fin n))
    (hA : ∀ r, (A r).card ≤ 2) (g : Fin m → (Fin n → Bool) → ℝ)
    (hg : ∀ r (x y : Fin n → Bool), (∀ i ∈ A r, x i = y i) → g r x = g r y)
    (S : Finset (Fin n)) (hS : 3 ≤ S.card) :
    ∑ U ∈ S.powerset, (-1 : ℝ) ^ (S.card - U.card) * ∑ r, g r (fun i => decide (i ∈ U)) = 0 := by sorry

end PromoMulti.PairwiseExact
