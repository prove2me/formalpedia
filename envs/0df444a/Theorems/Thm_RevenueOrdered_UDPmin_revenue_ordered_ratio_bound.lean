-- Prove2me | Theorems.Thm_RevenueOrdered_UDPmin_revenue_ordered_ratio_bound
-- name    : RevenueOrdered.UDPmin.revenue_ordered_ratio_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:56:31.526307+00:00
-- url     : https://prove2.me/theorems/d16a6001-6cdd-47f3-b6b1-cb3ff0673c40
-- title:
--   Theorem 3.2 — revenue-ordered assortments earn $\mathrm{OPT}/\sum_{i}(r_i-r_{i-1})/r_i\ge\mathrm{OPT}/(1+\ln(r_k/r_1))$
-- statement:
--   Let $\mathcal P$ be a regular discrete choice model on a finite nonempty product set $\mathcal C$, and $r:\mathcal C\to\mathbb R_{>0}$ a revenue function whose distinct values are $0<r_1<\dots<r_k$; put $r_0:=0$. Then the revenue-ordered value $\mathrm{RO}=\max_{i}\mathrm{rev}(S_i)$, $S_i=\{x:r(x)\ge r_i\}$, satisfies
--   $$\mathrm{OPT}\ \le\ \Big(\sum_{i=1}^k\frac{r_i-r_{i-1}}{r_i}\Big)\cdot\mathrm{RO}\qquad\text{and}\qquad \sum_{i=1}^k\frac{r_i-r_{i-1}}{r_i}\ \le\ 1+\ln\frac{r_k}{r_1}.$$
--   That is, revenue-ordered assortments approximate the optimum to within a factor $1/\sum_{i=1}^k (r_i-r_{i-1})/r_i\ \ge\ 1/(1+\ln\rho)$, $\rho=r_k/r_1$.
--
--   This is the guarantee that Corollary 4.7 transfers to uniform pricing through Theorem 4.6.
--
--   **Formalization Note** The approximation factor is stated in product form, $\mathrm{OPT}\le D\cdot\mathrm{RO}$, rather than as a ratio. This item restates, for this mission's own copy of the model, the goal theorem of mission I of the series (`RevenueOrdered.Ratio.revenue_ordered_ratio_bound`).
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 8, Theorem 3.2 (proof pp. 8–9)

import Mathlib
import Definitions.Def_RevenueOrdered_UDPmin_Model

namespace RevenueOrdered.UDPmin

/-- Theorem 3.2 (Berbeglia–Joret, arXiv:1606.01371v3, p. 8), for an arbitrary regular choice
model: `OPT ≤ (∑_{i=1}^{k} (r_i − r_{i−1})/r_i) · RO` and `∑_{i=1}^{k} (r_i − r_{i−1})/r_i ≤
1 + ln(r_k/r_1)`, with `r_0 := 0`. -/
theorem revenue_ordered_ratio_bound {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    (P : C → Finset C → ℝ) (hP : IsRegular P) (r : C → ℝ) (hr : ∀ x, 0 < r x) :
    RevenueOrdered.Ratio.opt P r ≤ ratioSum r * ro P r ∧
    ratioSum r ≤ 1 + Real.log (rMax r / rMin r) := by sorry

end RevenueOrdered.UDPmin
