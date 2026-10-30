-- Prove2me | Theorems.Thm_STPRideshare_Mechanism_theorem_2_envy_free_riders
-- name    : STPRideshare.Mechanism.theorem_2_envy_free_riders
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-30T04:19:00.862058+00:00
-- url     : https://prove2.me/theorems/9cf93846-a404-498e-a8d2-05a972f5a63a
-- title:
--   Theorem 2, p. 21 — from any history onward the STP outcome is envy-free for riders
-- statement:
--   Let the spatio-temporal pricing (STP) mechanism of Definition 12 (p. 21) be run with a selector that, for every valid economy, picks a welfare-optimal integral dispatching (an optimal solution of the ILP (4)–(8), equivalently by Lemma 2 of the LP (9)). Then the STP mechanism is **envy-free for riders**: for every valid economy, every rider $j$, every rider $j'$ requesting the same trip $(o_{j'},d_{j'},\tau_{j'})=(o_j,d_j,\tau_j)$ and every reachable history $h_{\tau_j}$, when all drivers follow the dispatches from $h_{\tau_j}$,
--
--   $$\hat x_{j'}v_j-\hat q_{j'}\;\le\;\hat x_j v_j-\hat q_j .$$
--
--   This is one part of the main result (Theorem 2) of the paper.
--
--   **Formalization Note.** This is one of the nine conjuncts of `STPRideshare.Mechanism.theorem_2` (Theorem 2, p. 21), stated with exactly the same definitions (`Definitions.Def_STPRideshare_Mechanism_STP`) and the same hypotheses: an arbitrary selector `sel` together with the hypothesis `IsOptimalSelector sel`.
-- source:
--   Ma, Fang, Parkes, Spatio-Temporal Pricing for Ridesharing Platforms, arXiv:1801.04015v5, p. 21, Theorem 2 (proof pp. 52–56); property defined in Definition 9, (26), p. 20

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_STP

namespace STPRideshare.Mechanism

/-- Theorem 2, p. 21 — from any history onward the STP outcome is envy-free for riders. -/
theorem theorem_2_envy_free_riders {L : Type} [Fintype L] (sel : Selector L) (hsel : IsOptimalSelector sel) :
    EnvyFreeRiders (stp sel) := by sorry

end STPRideshare.Mechanism
