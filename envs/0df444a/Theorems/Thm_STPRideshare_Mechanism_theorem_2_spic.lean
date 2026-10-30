-- Prove2me | Theorems.Thm_STPRideshare_Mechanism_theorem_2_spic
-- name    : STPRideshare.Mechanism.theorem_2_spic
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-30T04:19:29.53027+00:00
-- url     : https://prove2.me/theorems/9700ca04-1aee-4a68-8aab-523f1a74884e
-- title:
--   Theorem 2, p. 21 — the STP mechanism is subgame-perfect incentive compatible
-- statement:
--   Let the spatio-temporal pricing (STP) mechanism of Definition 12 (p. 21) be run with a selector that, for every valid economy, picks a welfare-optimal integral dispatching (an optimal solution of the ILP (4)–(8), equivalently by Lemma 2 of the LP (9)). Then the STP mechanism is **subgame-perfect incentive compatible**: for every valid economy, every reachable history $h_t$ with $t\le T-1$, every driver $i$ and every admissible strategy $\sigma_i$ of driver $i$,
--
--   $$\sum_{t'=t}^{T-1}\hat\pi_{i,t'}\big((\sigma_i,\sigma^*_{-i}),h_t\big)\;\le\;\sum_{t'=t}^{T-1}\hat\pi_{i,t'}\big(\sigma^*,h_t\big),$$
--
--   where $\sigma^*$ is the straightforward profile in which every driver follows the dispatches and $\hat\pi_{i,t'}$ is driver $i$'s realized payment minus cost at time $t'$. Thus following the dispatches from any history onward is a subgame-perfect equilibrium.
--
--   This is one part of the main result (Theorem 2) of the paper.
--
--   **Formalization Note.** This is one of the nine conjuncts of `STPRideshare.Mechanism.theorem_2` (Theorem 2, p. 21), stated with exactly the same definitions (`Definitions.Def_STPRideshare_Mechanism_STP`) and the same hypotheses: an arbitrary selector `sel` together with the hypothesis `IsOptimalSelector sel`.
-- source:
--   Ma, Fang, Parkes, Spatio-Temporal Pricing for Ridesharing Platforms, arXiv:1801.04015v5, p. 21, Theorem 2 (proof pp. 52–56); property defined in Definition 7, (23), p. 19

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_STP

namespace STPRideshare.Mechanism

/-- Theorem 2, p. 21 — the STP mechanism is subgame-perfect incentive compatible. -/
theorem theorem_2_spic {L : Type} [Fintype L] (sel : Selector L) (hsel : IsOptimalSelector sel) :
    SPIC (stp sel) := by sorry

end STPRideshare.Mechanism
