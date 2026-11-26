-- Prove2me | Theorems.Thm_TunnellChallenge_preferredTarget_bridge
-- name    : TunnellChallenge.preferredTarget_bridge
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:02:28.146891+00:00
-- url     : https://prove2.me/theorems/de32f352-9f08-55d9-bac3-93a9da9fd19f
-- title:
--   Tunnell Challenge: preferred Target bridge
-- statement:
--   The Tunnell Challenge construction uses the preferred Target bridge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L404-L427
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/Solution.lean#L404-L427

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution
set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial

theorem TunnellChallenge.preferredTarget_bridge {n : ℤ} (hpos : 0 < n)
    (s : BResidual n) (t : AResidual n) :
    arEquiv n (preferredTarget s t) =
      TunnellMap.preferredTarget (brEquiv n s) (arEquiv n t) := by sorry
