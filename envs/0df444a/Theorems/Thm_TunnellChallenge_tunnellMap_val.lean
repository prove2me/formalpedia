-- Prove2me | Theorems.Thm_TunnellChallenge_tunnellMap_val
-- name    : TunnellChallenge.tunnellMap_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:59:32.175744+00:00
-- url     : https://prove2.me/theorems/0f03dcb9-7687-481f-9542-f1fdfcbf6da1
-- title:
--   Tunnell Challenge: tunnell Map val
-- statement:
--   The coordinates of the image, in product form.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L602-L611
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L602-L611

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution
set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial

theorem TunnellChallenge.tunnellMap_val {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n)) (p : BRep n) :
    (tunnellMap hodd hpos hsq hbalance p).1 =
      ((TunnellMap.paperTunnellMapTotal hodd hpos hsq
          (balance_transport hbalance) (bEquiv n p)).1.x,
        (TunnellMap.paperTunnellMapTotal hodd hpos hsq
          (balance_transport hbalance) (bEquiv n p)).1.y,
        (TunnellMap.paperTunnellMapTotal hodd hpos hsq
          (balance_transport hbalance) (bEquiv n p)).1.z) := by sorry
