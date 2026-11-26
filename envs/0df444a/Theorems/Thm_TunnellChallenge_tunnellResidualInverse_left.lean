-- Prove2me | Theorems.Thm_TunnellChallenge_tunnellResidualInverse_left
-- name    : TunnellChallenge.tunnellResidualInverse_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:17:33.578742+00:00
-- url     : https://prove2.me/theorems/74e55d28-576a-5691-b904-34b148f6c14f
-- title:
--   Tunnell Challenge: tunnell Residual Inverse left
-- statement:
--   The Tunnell Challenge construction uses the tunnell Residual Inverse left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L569-L579
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L569-L579

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution
set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial

theorem TunnellChallenge.tunnellResidualInverse_left {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (s : BResidual n) :
    tunnellResidualInverse hodd hpos hsq hbalance
      (tunnellResidualMap hodd hpos hsq hbalance s) = s := by sorry
