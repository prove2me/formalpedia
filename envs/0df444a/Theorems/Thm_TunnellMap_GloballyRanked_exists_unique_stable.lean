-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_exists_unique_stable
-- name    : TunnellMap.GloballyRanked.exists_unique_stable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:38:47.446513+00:00
-- url     : https://prove2.me/theorems/d38c43b3-9d7d-58f4-9ae2-2f2881790f51
-- title:
--   Globally Ranked: exists unique stable
-- statement:
--   The Globally Ranked construction uses the exists unique stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/GloballyRankedExistence.lean#L123-L129
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/GloballyRankedExistence.lean#L123-L129

import Definitions.Def_TunnellMap_GloballyRanked
import Definitions.Def_TunnellMap_GloballyRankedExistence
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*}

theorem TunnellMap.GloballyRanked.exists_unique_stable [LinearOrder K] [Fintype S] [Fintype T]
    (I : GloballyRanked K S T) (hcard : Fintype.card S = Fintype.card T) :
    ∃! M : S ≃ T, I.Stable M := by sorry
