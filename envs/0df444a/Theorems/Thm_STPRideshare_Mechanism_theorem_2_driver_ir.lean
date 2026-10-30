-- Prove2me | Theorems.Thm_STPRideshare_Mechanism_theorem_2_driver_ir
-- name    : STPRideshare.Mechanism.theorem_2_driver_ir
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-30T04:19:11.137916+00:00
-- url     : https://prove2.me/theorems/926f598e-7c2a-4dc6-89d7-b2101eb95461
-- title:
--   Theorem 2, p. 21 — from any history onward the STP outcome is individually rational for drivers
-- statement:
--   Let the spatio-temporal pricing (STP) mechanism of Definition 12 (p. 21) be run with a selector that, for every valid economy, picks a welfare-optimal integral dispatching (an optimal solution of the ILP (4)–(8), equivalently by Lemma 2 of the LP (9)). Then the STP mechanism is **individually rational for drivers** from any history onward: for every valid economy, every reachable history $h_t$ with $t\le T-1$ and every driver $i$ who has not yet entered the platform (state $s_{i,t}=(0,\ell,\tau)$), her continuation utility when all drivers follow the dispatches is non-negative:
--
--   $$\sum_{t'=t}^{T-1}\hat\pi_{i,t'}(\sigma^*,h_t)\;\ge\;0 .$$
--
--   This is one part of the main result (Theorem 2) of the paper.
--
--   **Formalization Note.** This is one of the nine conjuncts of `STPRideshare.Mechanism.theorem_2` (Theorem 2, p. 21), stated with exactly the same definitions (`Definitions.Def_STPRideshare_Mechanism_STP`) and the same hypotheses: an arbitrary selector `sel` together with the hypothesis `IsOptimalSelector sel`.
-- source:
--   Ma, Fang, Parkes, Spatio-Temporal Pricing for Ridesharing Platforms, arXiv:1801.04015v5, p. 21, Theorem 2 (proof pp. 52–56); property defined in Definition 8 (ii), p. 19

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_STP

namespace STPRideshare.Mechanism

/-- Theorem 2, p. 21 — from any history onward the STP outcome is individually rational for drivers. -/
theorem theorem_2_driver_ir {L : Type} [Fintype L] (sel : Selector L) (hsel : IsOptimalSelector sel) :
    DriverIRFromAnyHistory (stp sel) := by sorry

end STPRideshare.Mechanism
