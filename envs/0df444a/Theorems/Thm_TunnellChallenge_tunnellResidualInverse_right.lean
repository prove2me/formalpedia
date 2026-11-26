-- Prove2me | Theorems.Thm_TunnellChallenge_tunnellResidualInverse_right
-- name    : TunnellChallenge.tunnellResidualInverse_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:17:54.510577+00:00
-- url     : https://prove2.me/theorems/00bac126-21a4-51be-8afe-22c49f92d31e
-- title:
--   Tunnell Challenge: tunnell Residual Inverse right
-- statement:
--   The Tunnell Challenge construction uses the tunnell Residual Inverse right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L581-L591
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L581-L591

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution
set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial

theorem TunnellChallenge.tunnellResidualInverse_right {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (t : AResidual n) :
    tunnellResidualMap hodd hpos hsq hbalance
      (tunnellResidualInverse hodd hpos hsq hbalance t) = t := by sorry
