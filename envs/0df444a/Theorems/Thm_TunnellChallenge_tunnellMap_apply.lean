-- Prove2me | Theorems.Thm_TunnellChallenge_tunnellMap_apply
-- name    : TunnellChallenge.tunnellMap_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:01:30.623229+00:00
-- url     : https://prove2.me/theorems/11c0b83b-9f76-4c94-8b1d-fda0c8905e5c
-- title:
--   Tunnell Challenge: tunnell Map apply
-- statement:
--   The Tunnell Challenge construction uses the tunnell Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L593-L599
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L593-L599

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution
set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial

theorem TunnellChallenge.tunnellMap_apply {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n)) (p : BRep n) :
    aEquiv n (tunnellMap hodd hpos hsq hbalance p) =
      TunnellMap.paperTunnellMapTotal hodd hpos hsq (balance_transport hbalance)
        (bEquiv n p) := by sorry
