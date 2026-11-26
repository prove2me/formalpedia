-- Prove2me | Theorems.Thm_TunnellMap_Examples41_sortedCounts_counts41
-- name    : TunnellMap.Examples41.sortedCounts_counts41
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:46:13.674932+00:00
-- url     : https://prove2.me/theorems/9c46cf3f-4184-5c44-849b-37bbdced2159
-- title:
--   Examples41: sorted Counts counts41
-- statement:
--   The Examples41 construction uses the sorted Counts counts41 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L137-L141
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L137-L141

import Definitions.Def_TunnellMap_Examples41Generator
import Definitions.Def_TunnellMap_Sharpness
import Definitions.Def_TunnellMap_Examples41Matching
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open GloballyRanked
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.sortedCounts_counts41 : sortedCounts [1, 3, 1, 1] = [1, 1, 1, 3] := by sorry
