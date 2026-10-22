-- Prove2me | Theorems.Thm_SearchDiscovery_Reservation_eq6_unique_solution
-- name    : SearchDiscovery.Reservation.eq6_unique_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:37.250876+00:00
-- url     : https://prove2.me/theorems/34fa8660-6bc6-4a47-b6d1-3722a99e9985
-- title:
--   (6), p. 12 — for each partial valuation the search value equation has a unique solution
-- statement:
--   In the search and discovery model, fix a partial valuation $x$ and let $Y\sim F_{Y\mid X=x}$. Recall the myopic net gain of inspection against an outside option $z$,
--   $$Q_s(x,c_s,z)=\mathbb E_Y\big[\max\{0,\,x+Y-z\}\big]-c_s .$$
--   Under the standing assumptions ($c_s>0$, finite mean and variance of $Y$ given $X=x$), the equation
--   $$Q_s(x,c_s,z)=0$$
--   has exactly one solution $z\in\mathbb R$. This solution is the **search value** $z^s$ of a product with partial valuation $x$.
--
--   The statement makes the search value well defined; every later statement takes a function $z^s$ satisfying (6) for all $x$ as a hypothesis, which by this result pins it down uniquely.
-- source:
--   Greminger, Optimal Search and Discovery, arXiv:1911.07773v5, p. 12, (6)

import Mathlib
import Definitions.Def_SearchDiscovery_Reservation_Model

namespace SearchDiscovery.Reservation

open MeasureTheory ProbabilityTheory

theorem eq6_unique_solution (M : SDModel) (hM : M.Standing) (x : ℝ) :
    ∃! z : ℝ, M.Qs x z = 0 := by sorry

end SearchDiscovery.Reservation
