-- Prove2me | Theorems.Thm_TunnellMap_Examples41_residual_proposal_trace41_value
-- name    : TunnellMap.Examples41.residual_proposal_trace41_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:21:28.34481+00:00
-- url     : https://prove2.me/theorems/5ac19be3-f523-4ecd-9b7f-de6d48fb5278
-- title:
--   Examples41: residual proposal trace41 value
-- statement:
--   The Examples41 construction uses the residual proposal trace41 value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L100-L102
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L100-L102

import Definitions.Def_TunnellMap_Examples41Generator
import Definitions.Def_TunnellMap_Sharpness
import Definitions.Def_TunnellMap_Examples41Matching
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open GloballyRanked
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.residual_proposal_trace41_value :
    residualProposalTrace41 =
      [(0, 0), (1, 0), (2, 3), (3, 2), (1, 3), (1, 1)] := by sorry
