-- Prove2me | Theorems.Thm_STPRideshare_Mechanism_theorem_2_temporally_consistent
-- name    : STPRideshare.Mechanism.theorem_2_temporally_consistent
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-30T04:18:58.233428+00:00
-- url     : https://prove2.me/theorems/e5987183-a4e2-48d9-ac57-9447ae7e584e
-- title:
--   Theorem 2, p. 21 — the STP mechanism is temporally consistent
-- statement:
--   Let the spatio-temporal pricing (STP) mechanism of Definition 12 (p. 21) be run with a selector that, for every valid economy, picks a welfare-optimal integral dispatching (an optimal solution of the ILP (4)–(8), equivalently by Lemma 2 of the LP (9)). Then the STP mechanism is **temporally consistent**: for every valid economy $E$, every reachable history $h_t=(\alpha_{t-1},h_{t-1})$ in which some driver's action $\alpha_{i,t-1}$ differs from her dispatch $\alpha^*_{i,t-1}(h_{t-1})$, the updated plan of the mechanism from $h_t$ onward (the outcome of following the dispatches from $h_t$, written as a plan $(x,\tilde z,q,r)$ of the time-shifted economy $E^{(t)}(s_t)$, with times shifted by $t$) coincides with the time-$0$ plan that the mechanism computes for the economy $E^{(t)}(s_t)$ itself:
--
--   $$\big(x^{(t)},\tilde z^{(t)},q^{(t)},r^{(t)}\big)(h_t)\;=\;\big(x,\tilde z,q,r\big)\big(E^{(t)}(s_t)\big).$$
--
--   Temporal consistency says that re-planning after a deviation is the same as starting the mechanism afresh in the economy that the deviation left behind.
--
--   This is one part of the main result (Theorem 2) of the paper.
--
--   **Formalization Note.** This is one of the nine conjuncts of `STPRideshare.Mechanism.theorem_2` (Theorem 2, p. 21), stated with exactly the same definitions (`Definitions.Def_STPRideshare_Mechanism_STP`) and the same hypotheses: an arbitrary selector `sel` together with the hypothesis `IsOptimalSelector sel`.
-- source:
--   Ma, Fang, Parkes, Spatio-Temporal Pricing for Ridesharing Platforms, arXiv:1801.04015v5, p. 21, Theorem 2 (proof pp. 52–56); property defined in Definition 11, p. 20

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_STP

namespace STPRideshare.Mechanism

/-- Theorem 2, p. 21 — the STP mechanism is temporally consistent. -/
theorem theorem_2_temporally_consistent {L : Type} [Fintype L] (sel : Selector L) (hsel : IsOptimalSelector sel) :
    TemporallyConsistent (stp sel) := by sorry

end STPRideshare.Mechanism
