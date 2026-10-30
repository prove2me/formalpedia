-- Prove2me | Theorems.Thm_STPRideshare_Mechanism_theorem_2_welfare_optimal
-- name    : STPRideshare.Mechanism.theorem_2_welfare_optimal
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-30T04:19:16.072197+00:00
-- url     : https://prove2.me/theorems/0f688e0e-acf5-4205-ae72-1caa76197619
-- title:
--   Theorem 2, p. 21 — from any history onward the STP outcome is welfare-optimal
-- statement:
--   Let the spatio-temporal pricing (STP) mechanism of Definition 12 (p. 21) be run with a selector that, for every valid economy, picks a welfare-optimal integral dispatching (an optimal solution of the ILP (4)–(8), equivalently by Lemma 2 of the LP (9)). Then **from any history onward, the equilibrium outcome is welfare optimal**: for every valid economy and every reachable history $h_t$ with $t\le T-1$, the dispatching $(x,\tilde z)$ realized from $h_t$ onward when all drivers follow the dispatches, viewed as a dispatching of the time-shifted economy $E^{(t)}(s_t)$, is feasible and has the highest welfare
--
--   $$\sum_j x_j v_j-\sum_i \lambda_i$$
--
--   among all feasible dispatchings of $E^{(t)}(s_t)$.
--
--   This is one part of the main result (Theorem 2) of the paper.
--
--   **Formalization Note.** This is one of the nine conjuncts of `STPRideshare.Mechanism.theorem_2` (Theorem 2, p. 21), stated with exactly the same definitions (`Definitions.Def_STPRideshare_Mechanism_STP`) and the same hypotheses: an arbitrary selector `sel` together with the hypothesis `IsOptimalSelector sel`.
-- source:
--   Ma, Fang, Parkes, Spatio-Temporal Pricing for Ridesharing Platforms, arXiv:1801.04015v5, p. 21, Theorem 2 (proof pp. 52–56); property defined in Theorem 2, p. 21

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_STP

namespace STPRideshare.Mechanism

/-- Theorem 2, p. 21 — from any history onward the STP outcome is welfare-optimal. -/
theorem theorem_2_welfare_optimal {L : Type} [Fintype L] (sel : Selector L) (hsel : IsOptimalSelector sel) :
    WelfareOptimalFromAnyHistory (stp sel) := by sorry

end STPRideshare.Mechanism
