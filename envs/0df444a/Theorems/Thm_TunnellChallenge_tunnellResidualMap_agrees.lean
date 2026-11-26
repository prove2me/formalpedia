-- Prove2me | Theorems.Thm_TunnellChallenge_tunnellResidualMap_agrees
-- name    : TunnellChallenge.tunnellResidualMap_agrees
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:19:18.531329+00:00
-- url     : https://prove2.me/theorems/b0afa5ec-cdd1-5ca7-8eb5-dd8088c4b542
-- title:
--   Tunnell Challenge: tunnell Residual Map agrees
-- statement:
--   The Tunnell Challenge construction uses the tunnell Residual Map agrees property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L760-L770
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L760-L770

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution
set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial

theorem TunnellChallenge.tunnellResidualMap_agrees {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (s : BResidual n) :
    (tunnellResidualMap hodd hpos hsq hbalance s).1 =
      tunnellMap hodd hpos hsq hbalance s.1.1 := by sorry
