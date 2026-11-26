-- Prove2me | Theorems.Thm_TunnellMap_Examples41_generated_row_targets
-- name    : TunnellMap.Examples41.generated_row_targets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:11:30.02782+00:00
-- url     : https://prove2.me/theorems/a3a15970-8f2e-556e-a340-297c83cae795
-- title:
--   Examples41: generated row targets
-- statement:
--   The Examples41 construction uses the generated row targets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Generator.lean#L102-L110
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Generator.lean#L102-L110

import Definitions.Def_TunnellMap_Examples41Residual
import Definitions.Def_TunnellMap_Examples41Generator
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open OrderedGenerator
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.generated_row_targets :
    targetValue s2 frame41 rowIndex1 = ⟨4, 3, 0⟩ ∧
      targetValue s2 frame41 rowIndex2 = ⟨0, 3, -4⟩ ∧
      targetValue s2 frame41 rowIndex3 = ⟨4, -3, 0⟩ ∧
      targetValue s2 frame41 rowIndex4 = ⟨0, -3, -4⟩ := by sorry
