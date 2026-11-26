-- Prove2me | Theorems.Thm_TunnellMap_directTargetUsed_iff
-- name    : TunnellMap.directTargetUsed_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:45:59.826772+00:00
-- url     : https://prove2.me/theorems/27bf162c-a6e2-47eb-b988-1cc2ac112964
-- title:
--   Tunnell Map: direct Target Used iff
-- statement:
--   The Tunnell Map construction uses the direct Target Used iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualTargetTest.lean#L47-L51
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualTargetTest.lean#L47-L51

import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_ResidualTargetTest
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.directTargetUsed_iff {n : ℤ} (p : ARep n) :
    DirectTargetUsed p ↔ ImageUsedTriple p.1 := by sorry
