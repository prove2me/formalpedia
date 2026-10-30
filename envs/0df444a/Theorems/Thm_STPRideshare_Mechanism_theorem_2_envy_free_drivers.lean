-- Prove2me | Theorems.Thm_STPRideshare_Mechanism_theorem_2_envy_free_drivers
-- name    : STPRideshare.Mechanism.theorem_2_envy_free_drivers
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-30T04:19:04.492757+00:00
-- url     : https://prove2.me/theorems/c72d3a17-c86d-4385-af29-a6f48ff504c9
-- title:
--   Theorem 2, p. 21 — from any history onward the STP outcome is envy-free for drivers
-- statement:
--   Let the spatio-temporal pricing (STP) mechanism of Definition 12 (p. 21) be run with a selector that, for every valid economy, picks a welfare-optimal integral dispatching (an optimal solution of the ILP (4)–(8), equivalently by Lemma 2 of the LP (9)). Then the STP mechanism is **envy-free for drivers** from any history onward: for every valid economy, every reachable history $h_t$ with $t\le T-1$, and any two drivers $i,i'$ in the same state $s_{i,t}=s_{i',t}$,
--
--   $$\sum_{t'=t}^{T-1}\hat\pi_{i,t'}(\sigma^*,h_t)\;=\;\sum_{t'=t}^{T-1}\hat\pi_{i',t'}(\sigma^*,h_t),$$
--
--   i.e. drivers in the same state get the same continuation utility when all drivers follow the dispatches.
--
--   This is one part of the main result (Theorem 2) of the paper.
--
--   **Formalization Note.** This is one of the nine conjuncts of `STPRideshare.Mechanism.theorem_2` (Theorem 2, p. 21), stated with exactly the same definitions (`Definitions.Def_STPRideshare_Mechanism_STP`) and the same hypotheses: an arbitrary selector `sel` together with the hypothesis `IsOptimalSelector sel`.
-- source:
--   Ma, Fang, Parkes, Spatio-Temporal Pricing for Ridesharing Platforms, arXiv:1801.04015v5, p. 21, Theorem 2 (proof pp. 52–56); property defined in Definition 9, (25), p. 20

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_STP

namespace STPRideshare.Mechanism

/-- Theorem 2, p. 21 — from any history onward the STP outcome is envy-free for drivers. -/
theorem theorem_2_envy_free_drivers {L : Type} [Fintype L] (sel : Selector L) (hsel : IsOptimalSelector sel) :
    EnvyFreeDrivers (stp sel) := by sorry

end STPRideshare.Mechanism
