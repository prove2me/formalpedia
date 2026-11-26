-- Prove2me | Theorems.Thm_TunnellChallenge_tunnellMap_even
-- name    : TunnellChallenge.tunnellMap_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:18:15.2298+00:00
-- url     : https://prove2.me/theorems/f583f29c-9ec5-593e-9480-6b1a7d94f64a
-- title:
--   Tunnell Challenge: tunnell Map even
-- statement:
--   **The even branch.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L652-L660
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L652-L660

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution
set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial

theorem TunnellChallenge.tunnellMap_even {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : p.1.2.2 % 2 = 0) :
    (tunnellMap hodd hpos hsq hbalance p).1 =
      (p.1.1, p.1.2.1, p.1.2.2 / 2) := by sorry
