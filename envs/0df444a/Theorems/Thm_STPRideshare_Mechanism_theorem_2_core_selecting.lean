-- Prove2me | Theorems.Thm_STPRideshare_Mechanism_theorem_2_core_selecting
-- name    : STPRideshare.Mechanism.theorem_2_core_selecting
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-30T04:19:02.569649+00:00
-- url     : https://prove2.me/theorems/0c14e68b-09a8-4a29-ba36-6640f1357eda
-- title:
--   Theorem 2, p. 21 — from any history onward the STP outcome is in the core
-- statement:
--   Let the spatio-temporal pricing (STP) mechanism of Definition 12 (p. 21) be run with a selector that, for every valid economy, picks a welfare-optimal integral dispatching (an optimal solution of the ILP (4)–(8), equivalently by Lemma 2 of the LP (9)). Then the STP mechanism is **core-selecting**: for every valid economy and every reachable history $h_t$ with $t\le T-1$, the outcome $(x,\tilde z,q,r)$ realized from $h_t$ onward when all drivers follow the dispatches, viewed as a plan of the time-shifted economy $E^{(t)}(s_t)$, is in the core: it is feasible, and no coalition of drivers $S$ and riders $U$ has a feasible, budget-balanced plan among themselves that gives every member at least her utility under the STP outcome and some member strictly more.
--
--   This is one part of the main result (Theorem 2) of the paper.
--
--   **Formalization Note.** This is one of the nine conjuncts of `STPRideshare.Mechanism.theorem_2` (Theorem 2, p. 21), stated with exactly the same definitions (`Definitions.Def_STPRideshare_Mechanism_STP`) and the same hypotheses: an arbitrary selector `sel` together with the hypothesis `IsOptimalSelector sel`.
-- source:
--   Ma, Fang, Parkes, Spatio-Temporal Pricing for Ridesharing Platforms, arXiv:1801.04015v5, p. 21, Theorem 2 (proof pp. 52–56); property defined in Definition 10, p. 20

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_STP

namespace STPRideshare.Mechanism

/-- Theorem 2, p. 21 — from any history onward the STP outcome is in the core. -/
theorem theorem_2_core_selecting {L : Type} [Fintype L] (sel : Selector L) (hsel : IsOptimalSelector sel) :
    CoreSelecting (stp sel) := by sorry

end STPRideshare.Mechanism
