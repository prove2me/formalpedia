-- Prove2me | Theorems.Thm_RetailVariety_Structure_eq_8_trend_newsvendor
-- name    : RetailVariety.Structure.eq_8_trend_newsvendor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:33.423679+00:00
-- url     : https://prove2.me/theorems/39eb788b-6d24-4797-9be8-1d74b365755a
-- title:
--   (8): under trend-following demand, stocking $\lambda$ iff $pq_j\ge c$ is optimal and the store profit is $\pi_T(S,v)$
-- statement:
--   Consider the trend-following population model. Let $v_j>0$, $v_0>0$, $0<c<p$ and $\lambda>0$, and fix an assortment $S$ with MNL shares $q_j=q_j(S)$. For $j\in S$ the demand $Y_j$ has the scaled Bernoulli law (3): $P(Y_j=\lambda)=q_j$, $P(Y_j=0)=1-q_j$. Let
--   $$x^*_j=\begin{cases}\lambda,& j\in S,\ pq_j\ge c,\\ 0,&\text{otherwise.}\end{cases}$$
--   Then $x^*$ maximizes $\sum_{j\in S}E[p\min\{x_j,Y_j\}-cx_j]$ over all $x\ge0$, and the maximum value is
--   $$\pi_T(S,v)=\sum_{j\in S}(pq_j-c)^+\lambda .$$
--
--   This identifies the closed-form profit (8) with the trend-following stocking problem.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1502, §2.4.2, eq. (8)

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_RetailVariety_Structure_Newsvendor

open MeasureTheory ProbabilityTheory

namespace RetailVariety.Structure

/-- (8), p. 1502: in the trend-following population model, with `Y_j` distributed as (3)
(`P(Y_j = λ) = q_j`, `P(Y_j = 0) = 1 - q_j`) for `j ∈ S`, the stocking vector
`x*_j = λ` if `p q_j ≥ c`, `x*_j = 0` if `p q_j < c` (and `x*_j = 0` for `j ∉ S`) maximizes
`∑_{j∈S} E[p min{x_j, Y_j} - c x_j]` over `x ≥ 0`, and the maximum is `π_T(S, v)` of (8). -/
theorem eq_8_trend_newsvendor {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ j, 0 < v j)
    (hv0 : 0 < v0) (p c lam : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (S : Finset (Fin n)) :
    IsMaxOn
        (fun x : Fin n → ℝ => ∑ j ∈ S,
          newsvendorProfit (trendDemand lam (share v v0 S j)) p c (x j))
        {x | ∀ j, 0 ≤ x j}
        (fun j => if j ∈ S ∧ c ≤ p * share v v0 S j then lam else 0) ∧
      ∑ j ∈ S, newsvendorProfit (trendDemand lam (share v v0 S j)) p c
          (if c ≤ p * share v v0 S j then lam else 0)
        = profitT p c lam v v0 S := by sorry

end RetailVariety.Structure
