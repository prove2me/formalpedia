-- Prove2me | Theorems.Thm_TunnellMap_Examples41_generated_row_directions
-- name    : TunnellMap.Examples41.generated_row_directions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:11:25.626635+00:00
-- url     : https://prove2.me/theorems/edffae28-4e0d-47d2-b18d-c468c5b965c6
-- title:
--   Examples41: generated row directions
-- statement:
--   The Examples41 construction uses the generated row directions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Generator.lean#L93-L100
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Generator.lean#L93-L100

import Definitions.Def_TunnellMap_Examples41Residual
import Definitions.Def_TunnellMap_Examples41Generator
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open OrderedGenerator
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.generated_row_directions :
    dValue frame41 rowIndex1 = ⟨1, -1, 1⟩ ∧
      dValue frame41 rowIndex2 = ⟨1, 1, 1⟩ ∧
      dValue frame41 rowIndex3 = ⟨1, -4, 1⟩ ∧
      dValue frame41 rowIndex4 = ⟨1, 4, 1⟩ := by sorry
