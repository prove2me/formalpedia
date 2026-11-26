-- Prove2me | Theorems.Thm_TunnellMap_direct_images_pairwise_disjoint
-- name    : TunnellMap.direct_images_pairwise_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:41:48.652819+00:00
-- url     : https://prove2.me/theorems/d3d3965b-bc9f-4b2a-a8f4-bbc145861427
-- title:
--   Tunnell Map: direct images pairwise disjoint
-- statement:
--   The Tunnell Map construction uses the direct images pairwise disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuarterTurns.lean#L433-L452
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuarterTurns.lean#L433-L452

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_QuarterTurns
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.direct_images_pairwise_disjoint {n : ℤ} (hn : Odd n) (p : ARep n) :
    ¬ (ImagePredicate1 p ∧ ImagePredicate2 p) ∧
      ¬ (ImagePredicate1 p ∧ ImagePredicate3 p) ∧
      ¬ (ImagePredicate2 p ∧ ImagePredicate3 p) := by sorry
