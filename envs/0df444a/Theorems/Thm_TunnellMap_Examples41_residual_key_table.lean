-- Prove2me | Theorems.Thm_TunnellMap_Examples41_residual_key_table
-- name    : TunnellMap.Examples41.residual_key_table
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:57:54.438049+00:00
-- url     : https://prove2.me/theorems/e458b8bf-077a-4ecf-ba55-9daced19c50a
-- title:
--   Examples41: residual key table
-- statement:
--   The Examples41 construction uses the residual key table property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L399-L419
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L399-L419

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.residual_key_table :
    representativeEdgeKey s1 t1 = key41 5 1 (-1) (-1) ∧
      representativeEdgeKey s1 t3 = key41 5 1 1 (-1) ∧
      representativeEdgeKey s1 t2 = key41 20 1 (-4) (-1) ∧
      representativeEdgeKey s1 t4 = key41 20 1 4 (-1) ∧
      representativeEdgeKey s2 t1 = key41 5 1 (-1) 1 ∧
      representativeEdgeKey s2 t4 = key41 5 1 1 1 ∧
      representativeEdgeKey s2 t2 = key41 20 1 (-4) 1 ∧
      representativeEdgeKey s2 t3 = key41 20 1 4 1 ∧
      representativeEdgeKey s3 t4 = key41 5 1 (-1) (-1) ∧
      representativeEdgeKey s3 t2 = key41 5 1 1 (-1) ∧
      representativeEdgeKey s3 t3 = key41 20 1 (-4) (-1) ∧
      representativeEdgeKey s3 t1 = key41 20 1 4 (-1) ∧
      representativeEdgeKey s4 t3 = key41 5 1 (-1) 1 ∧
      representativeEdgeKey s4 t2 = key41 5 1 1 1 ∧
      representativeEdgeKey s4 t4 = key41 20 1 (-4) 1 ∧
      representativeEdgeKey s4 t1 = key41 20 1 4 1 := by sorry
