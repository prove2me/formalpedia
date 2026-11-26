-- Prove2me | Theorems.Thm_TunnellChallenge_tunnellMap_quarterTurn_two
-- name    : TunnellChallenge.tunnellMap_quarterTurn_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:18:48.993646+00:00
-- url     : https://prove2.me/theorems/5333b8f8-414a-561e-b633-9507acc1afdb
-- title:
--   Tunnell Challenge: tunnell Map quarter Turn two
-- statement:
--   **The second quarter-turn.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L677-L689
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L677-L689

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution
set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial

theorem TunnellChallenge.tunnellMap_quarterTurn_two {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : ¬ p.1.2.2 % 2 = 0)
    (h₁ : ¬ (8 : ℤ) ∣ (p.1.1 + 2 * p.1.2.2 + p.1.2.1))
    (h₂ : (8 : ℤ) ∣ (p.1.2.1 - p.1.1 + 2 * p.1.2.2)) :
    (tunnellMap hodd hpos hsq hbalance p).1 =
      (p.1.1 - 2 * p.1.2.2 + 4 * ((p.1.2.1 - p.1.1 + 2 * p.1.2.2) / 8),
        -p.1.1 - 2 * p.1.2.2,
        (p.1.2.1 - p.1.1 + 2 * p.1.2.2) / 8) := by sorry
