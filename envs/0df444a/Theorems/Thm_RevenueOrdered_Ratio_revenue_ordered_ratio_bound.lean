-- Prove2me | Theorems.Thm_RevenueOrdered_Ratio_revenue_ordered_ratio_bound
-- name    : RevenueOrdered.Ratio.revenue_ordered_ratio_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:48:16.94441+00:00
-- url     : https://prove2.me/theorems/779221ce-1187-4f52-bb6c-2c53063fc323
-- title:
--   Theorem 3.2 — revenue-ordered assortments approximate OPT within 1/∑(r_i − r_{i−1})/r_i ≥ 1/(1 + ln(r_k/r_1))
-- statement:
--   Let $\mathcal P$ be a regular discrete choice model on a finite nonempty set of products $\mathcal C$ and $r:\mathcal C\to\mathbb R_{>0}$ a revenue function. Let $0<r_1<\cdots<r_k$ be the distinct values of $r$, $r_0:=0$, $\rho:=r_k/r_1$, $S_i=\{x : r(x)\ge r_i\}$ for $i\in[k]$, $\mathrm{RO}=\max_{i\in[k]}\operatorname{rev}(S_i)$ and $\mathrm{OPT}=\max_{S\subseteq\mathcal C}\operatorname{rev}(S)$. Then revenue-ordered assortments approximate the optimum revenue to within a factor of
--   $$
--   \frac{1}{\sum_{i=1}^{k}\frac{r_i-r_{i-1}}{r_i}}\;\ge\;\frac{1}{1+\ln\rho},
--   $$
--   that is,
--   $$
--   \mathrm{OPT}\;\le\;\Big(\sum_{i=1}^{k}\frac{r_i-r_{i-1}}{r_i}\Big)\,\mathrm{RO}
--   \qquad\text{and}\qquad
--   \sum_{i=1}^{k}\frac{r_i-r_{i-1}}{r_i}\;\le\;1+\ln\frac{r_k}{r_1}.
--   $$
--
--   This is the main guarantee of the paper's §3 (bound (B) of its introduction): the revenue-ordered heuristic loses at most a factor $1+\ln(r_k/r_1)$ under every regular choice model, a class that contains all random utility models. The sum form is the bound that the paper's Theorem 3.4 shows to be tight.
--
--   **Formalization Note** Both bounds are stated in product form. Since the sum is at least $1$ (its first term is $1$) and $1+\ln\rho\ge1$, this is equivalent to the paper's ratio formulation. The sum and the maximum run over the $k$ distinct revenue values with 1-based indices; $\ln$ is `Real.log`, applied to $r_k/r_1\ge1$.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 8, Theorem 3.2

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model
import Definitions.Def_RevenueOrdered_Ratio_RevenueOrdered

namespace RevenueOrdered.Ratio

/-- Theorem 3.2 (p. 8): revenue-ordered assortments approximate the optimum revenue to within a
factor of `1/∑_{i=1}^{k} (r_i − r_{i−1})/r_i ≥ 1/(1 + ln ρ)`, where `ρ := r_k/r_1` and
`r_0 := 0`. Stated in product form: `OPT ≤ (∑_{i=1}^{k} (r_i − r_{i−1})/r_i) · RO` and
`∑_{i=1}^{k} (r_i − r_{i−1})/r_i ≤ 1 + ln(r_k/r_1)`. -/
theorem revenue_ordered_ratio_bound {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    (P : C → Finset C → ℝ) (hP : IsRegular P) (r : C → ℝ) (hr : ∀ x, 0 < r x) :
    opt P r ≤ ratioSum r * roValue P r ∧
      ratioSum r ≤ 1 + Real.log (level r (numVals r) / level r 1) := by sorry

end RevenueOrdered.Ratio
