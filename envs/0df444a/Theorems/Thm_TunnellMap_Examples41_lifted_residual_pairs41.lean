-- Prove2me | Theorems.Thm_TunnellMap_Examples41_lifted_residual_pairs41
-- name    : TunnellMap.Examples41.lifted_residual_pairs41
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:22:52.274895+00:00
-- url     : https://prove2.me/theorems/7bdb3821-8348-541f-be97-74a6695974b8
-- title:
--   Examples41: lifted residual pairs41
-- statement:
--   The Examples41 construction uses the lifted residual pairs41 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L188-L196
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L188-L196

import Definitions.Def_TunnellMap_Examples41Generator
import Definitions.Def_TunnellMap_Sharpness
import Definitions.Def_TunnellMap_Examples41Matching
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open GloballyRanked
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.lifted_residual_pairs41 :
    residualTargetLift (preferredTarget s1 t1) = ⟨4, 3, 0⟩ ∧
      residualTargetLift (preferredTarget s2 t2) = ⟨4, -3, 0⟩ ∧
      residualTargetLift (preferredTarget s3 t4) = ⟨0, -3, 4⟩ ∧
      residualTargetLift (preferredTarget s4 t3) = ⟨0, -3, -4⟩ := by sorry
