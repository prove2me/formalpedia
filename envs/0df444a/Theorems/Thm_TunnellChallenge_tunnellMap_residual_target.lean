-- Prove2me | Theorems.Thm_TunnellChallenge_tunnellMap_residual_target
-- name    : TunnellChallenge.tunnellMap_residual_target
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:20:09.383861+00:00
-- url     : https://prove2.me/theorems/0606e70b-8e56-472b-86cf-5d004d198761
-- title:
--   Tunnell Challenge: tunnell Map residual target
-- statement:
--   **The residual branch lands in the residual targets.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L706-L721
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L706-L721

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution
set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial

theorem TunnellChallenge.tunnellMap_residual_target {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : ¬ p.1.2.2 % 2 = 0)
    (h₁ : ¬ (8 : ℤ) ∣ (p.1.1 + 2 * p.1.2.2 + p.1.2.1))
    (h₂ : ¬ (8 : ℤ) ∣ (p.1.2.1 - p.1.1 + 2 * p.1.2.2))
    (h₃ : ¬ (4 : ℤ) ∣ p.1.1) :
    ¬ DirectTargetUsed (tunnellMap hodd hpos hsq hbalance p) := by sorry
