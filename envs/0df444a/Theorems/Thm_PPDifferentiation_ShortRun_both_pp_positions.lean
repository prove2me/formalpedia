-- Prove2me | Theorems.Thm_PPDifferentiation_ShortRun_both_pp_positions
-- name    : PPDifferentiation.ShortRun.both_pp_positions
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T12:59:10.010122+00:00
-- url     : https://prove2.me/theorems/13032f77-db88-4fcd-8cc6-e48b7961b8bb
-- title:
--   §6 — both-PP positioning equilibrium and gross profits
-- statement:
--   For $t>0$, when both firms have already implemented personalized pricing, the positioning subgame has an equilibrium at $x_A=1/4$ and $x_B=3/4$. With the implementation costs already sunk, each firm's gross subgame profit is
--
--   $$\pi_A^{PP}=\pi_B^{PP}=\frac{t}{8}.$$
--
--   The equilibrium compares deviations to all real positions. These gross profits become the both-PP cell of the implementation game after subtracting $F$ from each firm.
--
--   **Formalization Note** The gross profit is the consumer-by-consumer Bertrand integral; the reservation value cancels under full coverage.
-- source:
--   Li, Wang, Nault, Is Personalized Pricing Profitable When Firms Can Differentiate?, working paper, SSRN abstract 3881900 (version of August 3, 2021), §6, pp. 23–24, “Both firms implement PP”

import Mathlib
import Definitions.Def_PPDifferentiation_ShortRun_Setting

namespace PPDifferentiation.ShortRun

theorem both_pp_positions (t : ℝ) (ht : 0 < t) :
    PPDifferentiation.Costless.IsPosEqPP t (1/4) (3/4) ∧
    PPDifferentiation.Costless.profPP t (1/4) (3/4) = t/8 ∧
    PPDifferentiation.Costless.profPP t (3/4) (1/4) = t/8 := by sorry

end PPDifferentiation.ShortRun
