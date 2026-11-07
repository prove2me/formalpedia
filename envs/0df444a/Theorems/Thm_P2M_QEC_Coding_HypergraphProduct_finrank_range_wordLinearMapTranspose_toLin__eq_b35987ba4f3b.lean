-- Prove2me | Theorems.Thm_P2M_QEC_Coding_HypergraphProduct_finrank_range_wordLinearMapTranspose_toLin__eq_b35987ba4f3b
-- name    : P2M_QEC_Coding_HypergraphProduct_finrank_range_wordLinearMapTranspose_toLin__eq_b35987ba4f3b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:36:39.822217+00:00
-- url     : https://prove2.me/theorems/2aebd535-e173-44b5-8266-9823132895c4
-- title:
--   P2 M QEC Coding Hypergraph Product finrank range word Linear Map Transpose to Lin  eq b35987ba4f3b: P2 M QEC Coding Hypergraph Product finrank range word Linear Map Transpose to Lin  eq b35987ba4f3b
-- statement:
--   Transposing a finite matrix-defined word map preserves its rank.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/Formula.lean#L181-L192
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/Formula.lean#L181-L192

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_BoundaryMaps
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Formula
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem P2M_QEC_Coding_HypergraphProduct_finrank_range_wordLinearMapTranspose_toLin__eq_b35987ba4f3b
    {F : Type v} {row col : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype row] [DecidableEq row]
    [Fintype col] [DecidableEq col]
    (M : Matrix row col F) :
    Module.finrank F
        (LinearMap.range (wordLinearMapTranspose (Matrix.toLin' M))) =
      Module.finrank F (LinearMap.range (Matrix.toLin' M)) := by sorry

alias «QEC».«Coding».«HypergraphProduct».«finrank_range_wordLinearMapTranspose_toLin'_eq» := P2M_QEC_Coding_HypergraphProduct_finrank_range_wordLinearMapTranspose_toLin__eq_b35987ba4f3b
