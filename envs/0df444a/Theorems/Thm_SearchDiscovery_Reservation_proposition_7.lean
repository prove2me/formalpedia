-- Prove2me | Theorems.Thm_SearchDiscovery_Reservation_proposition_7
-- name    : SearchDiscovery.Reservation.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:47.272123+00:00
-- url     : https://prove2.me/theorems/6537a864-9db2-48f8-bed0-019cfc45b0a8
-- title:
--   Proposition 7, p. 42 — the discovery value equation (10) has a unique solution
-- statement:
--   Under the standing assumptions of the search and discovery model ($c_s,c_d>0$, $n_d\ge1$, finite means and variances), the equation
--   $$Q_d(c_d,c_s,z)=0,$$
--   which is (10), has exactly one solution $z\in\mathbb R$. This solution is the **discovery value** $z^d$.
--
--   Here $Q_d(c_d,c_s,z)$ is the expected optimal value of discovering $n_d$ products and searching only among them against an outside option $z$, minus $z$ and minus $c_d$, (9). The result makes the discovery value, the third reservation value of Theorem 1, well defined.
-- source:
--   Greminger, Optimal Search and Discovery, arXiv:1911.07773v5, p. 42, Appendix A.9, Proposition 7

import Mathlib
import Definitions.Def_SearchDiscovery_Reservation_Model

namespace SearchDiscovery.Reservation

open MeasureTheory ProbabilityTheory

theorem proposition_7 (M : SDModel) (hM : M.Standing) :
    ∃! z : ℝ, M.Qd z = 0 := by sorry

end SearchDiscovery.Reservation
