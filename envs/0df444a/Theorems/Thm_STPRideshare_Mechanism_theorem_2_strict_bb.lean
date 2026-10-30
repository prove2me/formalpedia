-- Prove2me | Theorems.Thm_STPRideshare_Mechanism_theorem_2_strict_bb
-- name    : STPRideshare.Mechanism.theorem_2_strict_bb
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-30T04:19:22.709699+00:00
-- url     : https://prove2.me/theorems/d95fe40a-db26-4ed2-8c61-79b2880f6b2d
-- title:
--   Theorem 2, p. 21 — the STP mechanism is strictly budget balanced
-- statement:
--   Let the spatio-temporal pricing (STP) mechanism of Definition 12 (p. 21) be run with a selector that, for every valid economy, picks a welfare-optimal integral dispatching (an optimal solution of the ILP (4)–(8), equivalently by Lemma 2 of the LP (9)). Then the STP mechanism is **strictly budget balanced** for every action profile of the drivers: for every valid economy and every admissible strategy profile $\sigma$ of the drivers,
--
--   $$\sum_{j\in\mathcal R}\hat q_j(\sigma)\;=\;\sum_{i\in\mathcal D}\hat r_i(\sigma),$$
--
--   where $\hat q_j(\sigma)$ is rider $j$'s payment and $\hat r_i(\sigma)=\sum_{t=0}^{T-1}\hat r_{i,t}$ is the total payment made to driver $i$.
--
--   This is one part of the main result (Theorem 2) of the paper.
--
--   **Formalization Note.** This is one of the nine conjuncts of `STPRideshare.Mechanism.theorem_2` (Theorem 2, p. 21), stated with exactly the same definitions (`Definitions.Def_STPRideshare_Mechanism_STP`) and the same hypotheses: an arbitrary selector `sel` together with the hypothesis `IsOptimalSelector sel`.
-- source:
--   Ma, Fang, Parkes, Spatio-Temporal Pricing for Ridesharing Platforms, arXiv:1801.04015v5, p. 21, Theorem 2 (proof pp. 52–56); property defined in Definition 6, p. 19

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_STP

namespace STPRideshare.Mechanism

/-- Theorem 2, p. 21 — the STP mechanism is strictly budget balanced. -/
theorem theorem_2_strict_bb {L : Type} [Fintype L] (sel : Selector L) (hsel : IsOptimalSelector sel) :
    StrictBB (stp sel) := by sorry

end STPRideshare.Mechanism
