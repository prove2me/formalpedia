-- Prove2me | Theorems.Thm_RevenueOrdered_Tightness_revenue_ordered_bounds_tight
-- name    : RevenueOrdered.Tightness.revenue_ordered_bounds_tight
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:19:17.591726+00:00
-- url     : https://prove2.me/theorems/be4977f1-75c4-4710-9f78-d8d02d498716
-- title:
--   Theorem 3.4 — the three revenue-ordered approximation bounds are tight
-- statement:
--   Section 3 proves three guarantees for the revenue-ordered assortments strategy under any regular discrete choice model with positive revenues taking $k$ distinct values $r_1<\dots<r_k$ ($r_0=0$):
--   1. (A) $\mathrm{OPT}\le k\cdot\mathrm{RO}$ (Theorem 3.1);
--   2. (B) $\mathrm{OPT}\le D_r\cdot\mathrm{RO}$ with $D_r=\sum_{i=1}^k (r_i-r_{i-1})/r_i$ (Theorem 3.2);
--   3. (C) $\mathrm{OPT}\le D_N(S^*)\cdot\mathrm{RO}$ with $D_N(S^*)=\sum_{i=1}^{\ell}(N_i-N_{i+1})/N_i$, for an optimal $S^*$ with $N_1>0$ (Theorem 3.3).
--
--   **Theorem 3.4.** All three bounds are tight: for every $k\ge1$ and every $\delta>0$ there exist a finite nonempty product set $\mathcal C$, a regular discrete choice model $\mathcal P$ on it, revenues $r:\mathcal C\to\mathbb R_{>0}$ taking exactly $k$ distinct values, and an optimal assortment $S^*$ ($\mathrm{rev}(S^*)=\mathrm{OPT}$) with $N_1>0$, such that simultaneously
--   $$
--   k\cdot\mathrm{RO}<(1+\delta)\,\mathrm{OPT},\qquad D_r\cdot\mathrm{RO}<(1+\delta)\,\mathrm{OPT},\qquad D_N(S^*)\cdot\mathrm{RO}<(1+\delta)\,\mathrm{OPT}.
--   $$
--   In other words, none of the three bounds remains true when multiplied by a factor $1+\delta$, for any number $k$ of distinct revenues.
--
--   The result shows that the analysis of §3 cannot be improved in terms of the parameters $k$, $D_r$ or $D_N$.
--
--   **Formalization Note** The bounds are stated multiplicatively, $\mathrm{OPT}\le D\cdot\mathrm{RO}$, so tightness is $D\cdot\mathrm{RO}<(1+\delta)\mathrm{OPT}$. The product set is an existentially quantified `Type` with `Fintype`, `DecidableEq` and `Nonempty` instances. $N_1>0$ is stated through the $0$-based index $0$. Tightness of the logarithmic forms $1/(1+\ln(r_k/r_1))$ and $1/(1+\ln\nu)$ is not claimed: the paper's instance does not show it.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 10, Theorem 3.4 (with p. 3, §1.1, for the meaning of tight)

import Mathlib
import Definitions.Def_RevenueOrdered_Tightness_ChoiceModel
import Definitions.Def_RevenueOrdered_Tightness_RevenueOrdered
import Definitions.Def_RevenueOrdered_Tightness_TightInstance

namespace RevenueOrdered.Tightness

/-- Theorem 3.4 (p. 10): the three bounds (A) `OPT ⩽ k · RO`, (B) `OPT ⩽ D_r · RO` and
(C) `OPT ⩽ D_N(S^*) · RO` are tight: for every `k ⩾ 1` and every `δ > 0` there is a regular
discrete choice model with positive revenues taking exactly `k` distinct values, and an optimal
assortment `S^*` with `N_1 > 0`, on which none of the three bounds holds when multiplied by
`1 + δ`. -/
theorem revenue_ordered_bounds_tight (k : ℕ) (hk : 1 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (C : Type) (_ : Fintype C) (_ : DecidableEq C) (_ : Nonempty C)
      (P : C → Finset C → ℝ) (r : C → ℝ) (Sstar : Finset C),
      IsRegular P ∧ (∀ x, 0 < r x) ∧ numRevenues r = k ∧
      rev P r Sstar = RevenueOrdered.Ratio.opt P r ∧
      (∃ i : Fin (numRevenues r), i.val = 0 ∧ 0 < purchaseAbove P r Sstar i) ∧
      (k : ℝ) * roValue P r < (1 + δ) * RevenueOrdered.Ratio.opt P r ∧
      revenueGapSum r * roValue P r < (1 + δ) * RevenueOrdered.Ratio.opt P r ∧
      purchaseGapSum P r Sstar * roValue P r < (1 + δ) * RevenueOrdered.Ratio.opt P r := by sorry

end RevenueOrdered.Tightness
