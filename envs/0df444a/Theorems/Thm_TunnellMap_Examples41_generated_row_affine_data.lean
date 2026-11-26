-- Prove2me | Theorems.Thm_TunnellMap_Examples41_generated_row_affine_data
-- name    : TunnellMap.Examples41.generated_row_affine_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:11:42.988509+00:00
-- url     : https://prove2.me/theorems/e8a680a4-fba5-4527-bfbf-84a67ca7c533
-- title:
--   Examples41: generated row affine data
-- statement:
--   The Examples41 construction uses the generated row affine data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Generator.lean#L86-L91
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Generator.lean#L86-L91

import Definitions.Def_TunnellMap_Examples41Residual
import Definitions.Def_TunnellMap_Examples41Generator
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open OrderedGenerator
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.generated_row_affine_data :
    (rowIndex1.A, rowIndex1.q, rowIndex1.u, rowIndex1.b) = (5, 1, 2, -1) ∧
      (rowIndex2.A, rowIndex2.q, rowIndex2.u, rowIndex2.b) = (5, -1, 2, 1) ∧
      (rowIndex3.A, rowIndex3.q, rowIndex3.u, rowIndex3.b) = (20, 1, 2, -4) ∧
      (rowIndex4.A, rowIndex4.q, rowIndex4.u, rowIndex4.b) = (20, -1, 2, 4) := by sorry
