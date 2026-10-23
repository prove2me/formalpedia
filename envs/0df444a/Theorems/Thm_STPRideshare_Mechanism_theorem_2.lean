-- Prove2me | Theorems.Thm_STPRideshare_Mechanism_theorem_2
-- name    : STPRideshare.Mechanism.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:13.702616+00:00
-- url     : https://prove2.me/theorems/cb7f96cc-a178-407e-9a9c-facdfe0d45dc
-- title:
--   Theorem 2, p. 21 — the STP mechanism is temporally consistent and SPIC, rider-IR and strictly BB, and from any history welfare-optimal, core-selecting, envy-free and driver-IR
-- statement:
--   Let the spatio-temporal pricing (STP) mechanism be run with any selector that picks a welfare-optimal integral dispatching of every valid economy. Then, for every valid economy:
--
--   1. the mechanism is **temporally consistent**: after a deviation at time $t-1$, the updated plan coincides with the plan the mechanism computes at time $0$ for the time-shifted economy $E^{(t)}(s_t)$;
--   2. it is **subgame-perfect incentive compatible**: from every reachable history $h_t$, $t\le T-1$, no driver can raise her continuation utility $\sum_{t'=t}^{T-1}\hat\pi_{i,t'}$ by any strategy when the other drivers follow the dispatches;
--   3. it is **individually rational for riders**, $\hat x_j(\sigma)v_j\ge\hat q_j(\sigma)$, and **strictly budget balanced**, $\sum_j\hat q_j(\sigma)=\sum_i\hat r_i(\sigma)$, for every strategy profile $\sigma$ of the drivers;
--   4. from every reachable history onward, the outcome when all drivers follow the dispatches is **welfare-optimal** for $E^{(t)}(s_t)$, **in the core**, **envy-free** for drivers in the same state and for riders requesting the same trip, and **individually rational for drivers** who have not yet entered.
--
--   This is the main result of the paper: re-planning with replica-gain prices after any deviation, without penalties or long-term contracts, makes following the dispatch a subgame-perfect equilibrium.
--
--   **Formalization Note.** Definition 12 computes "an optimal solution" without saying which, so the theorem is claimed for every optimal selector. Definitions 8–10 include SPIC as their condition (i); SPIC appears once here, and the other properties state condition (ii). Driver IR is read from any history onward, as the theorem states it. The p. 20 slip in $E^{(t)}(s_t)$ is corrected (an available driver who has not entered keeps $\beta=0$). Strategies are arbitrary admissible strategies, not only one-shot deviations.
-- source:
--   Ma, Fang, Parkes, Spatio-Temporal Pricing for Ridesharing Platforms, arXiv:1801.04015v5, p. 21, Theorem 2 (proof pp. 52–56)

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_STP

namespace STPRideshare.Mechanism

/-- Theorem 2, p. 21: for every selector of welfare-optimal integral dispatchings, the STP
mechanism is temporally consistent and SPIC, individually rational for riders and strictly budget
balanced for every admissible strategy profile, and from every history onward its `σ*` outcome is
welfare-optimal, in the core, envy-free (drivers and riders) and individually rational for
drivers. -/
theorem theorem_2 {L : Type} [Fintype L] (sel : Selector L) (hsel : IsOptimalSelector sel) :
    TemporallyConsistent (stp sel) ∧ SPIC (stp sel) ∧
    RiderIR (stp sel) ∧ StrictBB (stp sel) ∧
    WelfareOptimalFromAnyHistory (stp sel) ∧ CoreSelecting (stp sel) ∧
    EnvyFreeDrivers (stp sel) ∧ EnvyFreeRiders (stp sel) ∧
    DriverIRFromAnyHistory (stp sel) := by sorry

end STPRideshare.Mechanism
