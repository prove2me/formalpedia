-- Prove2me | Theorems.Thm_SunkCost_SmallBias_eq_4_demand
-- name    : SunkCost.SmallBias.eq_4_demand
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:45.910269+00:00
-- url     : https://prove2.me/theorems/607c3748-a89d-46e3-885d-1f769b865942
-- title:
--   Eq. (4), p. 8 (PDF 9) — demand is max(0, F(v2) − F(max(v1, v3))) + max(0, 1 − F(max(v2, v4)))
-- statement:
--   In the model of Jain and Chen, let the standing assumptions hold, let $F$ be a valuation distribution with support $(0,1)$, and let $\lambda\ge 0$ and $p\ge 0$. Then the demand at price $p$ is
--
--   $$D(p)=\max\bigl(0,\,F(v_2)-F(\max(v_1,v_3))\bigr)+\max\bigl(0,\,1-F(\max(v_2,v_4))\bigr),$$
--
--   where $v_1=(\kappa-\lambda p)/\beta$, $v_2=(1-\lambda p)/\beta$, $v_3=p/\alpha+\kappa$ and $v_4=p+\alpha\kappa+(1-\alpha)$.
--
--   The first term is the demand of the consumers who use the product only when the effort cost is low; the second is that of the consumers who always use it. The formula turns the primitive purchase rule into an explicit function of $F$ and is the starting point for Propositions 1 and 2.
--
--   **Formalization Note.** Demand is the $F$-measure of the set of valuations in $[0,1]$ whose anticipated utility (2)/(3) is positive; the theorem identifies it with the right-hand side of (4). The price and the bias are nonnegative, as in the paper.
-- source:
--   Jain and Chen, Sunk cost bias and time inconsistency: a strategic analysis of pricing decisions, Management Science, Articles in Advance (2022), doi:10.1287/mnsc.2022.4479, p. 8 (PDF 9), §4.1, eq. (4)

import Mathlib
import Definitions.Def_SunkCost_SmallBias_Model

namespace SunkCost.SmallBias

/-- Eq. (4), §4.1, p. 8 (PDF 9): for every sunk-cost bias `λ ≥ 0` and price `p ≥ 0`, the
demand (the `F`-mass of the consumers whose anticipated utility (2)/(3) is positive) is
`max(0, F(v₂) − F(max(v₁, v₃))) + max(0, 1 − F(max(v₂, v₄)))`. -/
theorem eq_4_demand (P : Params) (hS : P.Standing) (F : StieltjesFunction ℝ)
    (hF : ValuationCDF F) (lam p : ℝ) (hlam : 0 ≤ lam) (hp : 0 ≤ p) :
    demand P F lam p =
      max 0 (F (v2 P lam p) - F (max (v1 P lam p) (v3 P p))) +
        max 0 (1 - F (max (v2 P lam p) (v4 P p))) := by sorry

end SunkCost.SmallBias
