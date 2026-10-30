-- Prove2me | Theorems.Thm_STPRideshare_Mechanism_theorem_2_rider_ir
-- name    : STPRideshare.Mechanism.theorem_2_rider_ir
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-30T04:19:18.270039+00:00
-- url     : https://prove2.me/theorems/57064910-100d-4e59-b17c-61f4e168757c
-- title:
--   Theorem 2, p. 21 — the STP mechanism is individually rational for riders
-- statement:
--   Let the spatio-temporal pricing (STP) mechanism of Definition 12 (p. 21) be run with a selector that, for every valid economy, picks a welfare-optimal integral dispatching (an optimal solution of the ILP (4)–(8), equivalently by Lemma 2 of the LP (9)). Then the STP mechanism is **individually rational for riders** for every action profile of the drivers: for every valid economy, every admissible strategy profile $\sigma$ of the drivers and every rider $j$,
--
--   $$\hat q_j(\sigma)\;\le\;\hat x_j(\sigma)\,v_j,$$
--
--   where $\hat x_j(\sigma)$ counts the drivers who pick up rider $j$ at time $\tau_j$ and $\hat q_j(\sigma)$ is the payment charged to rider $j$.
--
--   This is one part of the main result (Theorem 2) of the paper.
--
--   **Formalization Note.** This is one of the nine conjuncts of `STPRideshare.Mechanism.theorem_2` (Theorem 2, p. 21), stated with exactly the same definitions (`Definitions.Def_STPRideshare_Mechanism_STP`) and the same hypotheses: an arbitrary selector `sel` together with the hypothesis `IsOptimalSelector sel`.
-- source:
--   Ma, Fang, Parkes, Spatio-Temporal Pricing for Ridesharing Platforms, arXiv:1801.04015v5, p. 21, Theorem 2 (proof pp. 52–56); property defined in (24), p. 19

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_STP

namespace STPRideshare.Mechanism

/-- Theorem 2, p. 21 — the STP mechanism is individually rational for riders. -/
theorem theorem_2_rider_ir {L : Type} [Fintype L] (sel : Selector L) (hsel : IsOptimalSelector sel) :
    RiderIR (stp sel) := by sorry

end STPRideshare.Mechanism
