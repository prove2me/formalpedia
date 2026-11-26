-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_stable_unique
-- name    : TunnellMap.GloballyRanked.stable_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:37:26.63022+00:00
-- url     : https://prove2.me/theorems/e0c123eb-2370-4b08-9510-fb7e7e9551ad
-- title:
--   Globally Ranked: stable unique
-- statement:
--   The Globally Ranked construction uses the stable unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/GloballyRanked.lean#L42-L119
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/GloballyRanked.lean#L42-L119

import Mathlib
import Definitions.Def_TunnellMap_GloballyRanked
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*}
variable [LinearOrder K] [Fintype S] [Fintype T]

theorem TunnellMap.GloballyRanked.stable_unique (I : GloballyRanked K S T) (M N : S ≃ T)
    (hM : I.Stable M) (hN : I.Stable N) : M = N := by sorry
