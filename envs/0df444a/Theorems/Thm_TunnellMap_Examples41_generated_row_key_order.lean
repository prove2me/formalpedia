-- Prove2me | Theorems.Thm_TunnellMap_Examples41_generated_row_key_order
-- name    : TunnellMap.Examples41.generated_row_key_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:11:51.935481+00:00
-- url     : https://prove2.me/theorems/ab078df4-ddf3-45d9-9413-6e14e8ff11c9
-- title:
--   Examples41: generated row key order
-- statement:
--   The Examples41 construction uses the generated row key order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Generator.lean#L112-L117
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Generator.lean#L112-L117

import Definitions.Def_TunnellMap_Examples41Residual
import Definitions.Def_TunnellMap_Examples41Generator
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open OrderedGenerator
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.generated_row_key_order :
    representativeEdgeKey s2 t1 < representativeEdgeKey s2 t4 ∧
      representativeEdgeKey s2 t4 < representativeEdgeKey s2 t2 ∧
      representativeEdgeKey s2 t2 < representativeEdgeKey s2 t3 := by sorry
