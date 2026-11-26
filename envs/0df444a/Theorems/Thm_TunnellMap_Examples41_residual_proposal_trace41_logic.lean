-- Prove2me | Theorems.Thm_TunnellMap_Examples41_residual_proposal_trace41_logic
-- name    : TunnellMap.Examples41.residual_proposal_trace41_logic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:21:15.275001+00:00
-- url     : https://prove2.me/theorems/d99ab7d0-b3ef-5c28-835c-a99a08551ccf
-- title:
--   Examples41: residual proposal trace41 logic
-- statement:
--   Each source proposes in row order, while `t1` retains `s1` over `s2`
--   and `t4` retains `s3` over `s2`.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L106-L114
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L106-L114

import Definitions.Def_TunnellMap_Examples41Generator
import Definitions.Def_TunnellMap_Sharpness
import Definitions.Def_TunnellMap_Examples41Matching
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open GloballyRanked
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.residual_proposal_trace41_logic :
    residualRank41 0 0 < residualRank41 0 2 ∧
      residualRank41 1 0 < residualRank41 1 3 ∧
      residualRank41 1 3 < residualRank41 1 1 ∧
      residualRank41 2 3 < residualRank41 2 1 ∧
      residualRank41 3 2 < residualRank41 3 1 ∧
      residualRank41 0 0 < residualRank41 1 0 ∧
      residualRank41 2 3 < residualRank41 1 3 := by sorry
