-- Prove2me | Theorems.Thm_TeamDelegation_Optimal_surplus_characterisation
-- name    : TeamDelegation.Optimal.surplus_characterisation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:23.141173+00:00
-- url     : https://prove2.me/theorems/5971f536-8b15-4f62-a05a-738fe9c0c07e
-- title:
--   Equations (59)–(66): characterisation of maximal agent surplus
-- statement:
--   In the regime $\Delta_A\le\Delta_A^{\mathrm{crit}}$ and $\Delta_{\mathrm{sum}}=\Delta_A+\Delta_B\ge0$, let $w_A,w_B$ be any success bonuses (whether or not they can be implemented as an equilibrium). In each of the two states, both working with the correct method maximises their combined one-period expected utility over every feasible pure delegated outcome if and only if all eight inequalities (59)–(66) hold:
--
--   $$\operatorname{SurplusMax}\quad\Longleftrightarrow\quad\bigwedge_{j=59}^{66}(j).$$
--
--   The eight inequalities compare the desired profile with one-worker, zero-worker and incorrect-method profiles. They are the paper's bridge from outcomes to the collusion argument.
--
--   **Formalization Note** The inequalities are bundled in the definition `SurplusConstraints`, with their eight formulas and order preserved.
-- source:
--   Upton, Implicit Incentives and Delegation in Teams, TRR 266 Working Paper No. 67 (SSRN 3991736, 17 Dec 2021), p. 38 (PDF 39), proof of Proposition 7, equations (59)–(66)

import Mathlib
import Definitions.Def_TeamDelegation_Optimal_Model

namespace TeamDelegation.Optimal

/-- Proof of Proposition 7, equations (59)–(66): in the regime of the
proof, for any success bonuses `wA, wB` (whether or not they implement anything),
the eight inequalities exactly characterize statewise surplus maximization. -/
theorem surplus_characterisation (P : Params) (hS : P.Standing)
    (hA1 : P.Assumption1) (c1A c1B ΔA ΔB wA wB : ℝ)
    (hA : ΔA ≤ DeltaCritA P) (hsum : 0 ≤ ΔA + ΔB) :
    SurplusMax P (Costs.ofDeltas c1A c1B ΔA ΔB) .deleg wA wB ↔
      SurplusConstraints P (wA + wB) (ΔA + ΔB) := by sorry

end TeamDelegation.Optimal
