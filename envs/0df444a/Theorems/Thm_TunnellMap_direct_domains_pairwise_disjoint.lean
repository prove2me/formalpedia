-- Prove2me | Theorems.Thm_TunnellMap_direct_domains_pairwise_disjoint
-- name    : TunnellMap.direct_domains_pairwise_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:41:37.647699+00:00
-- url     : https://prove2.me/theorems/66bbe6a0-2966-4abf-b639-43f0ad7cf910
-- title:
--   Tunnell Map: direct domains pairwise disjoint
-- statement:
--   The Tunnell Map construction uses the direct domains pairwise disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuarterTurns.lean#L408-L422
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuarterTurns.lean#L408-L422

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_QuarterTurns
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.direct_domains_pairwise_disjoint {n : ℤ} (hn : Odd n) (p : BOddRep n) :
    ¬ (DirectPredicate1 p ∧ DirectPredicate2 p) ∧
      ¬ (DirectPredicate1 p ∧ DirectPredicate3 p) ∧
      ¬ (DirectPredicate2 p ∧ DirectPredicate3 p) := by sorry
