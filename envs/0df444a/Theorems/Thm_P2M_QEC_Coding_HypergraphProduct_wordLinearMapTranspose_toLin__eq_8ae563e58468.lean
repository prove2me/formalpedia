-- Prove2me | Theorems.Thm_P2M_QEC_Coding_HypergraphProduct_wordLinearMapTranspose_toLin__eq_8ae563e58468
-- name    : P2M_QEC_Coding_HypergraphProduct_wordLinearMapTranspose_toLin__eq_8ae563e58468
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:37:22.411257+00:00
-- url     : https://prove2.me/theorems/183ad2c1-cab3-4f6f-910e-fb10cf291000
-- title:
--   P2 M QEC Coding Hypergraph Product word Linear Map Transpose to Lin  eq 8ae563e58468: P2 M QEC Coding Hypergraph Product word Linear Map Transpose to Lin  eq 8ae563e58468
-- statement:
--   The project transpose of a matrix-defined word map is the word map of the
--   transposed matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/Formula.lean#L157-L169
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/Formula.lean#L157-L169

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_BoundaryMaps
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Formula
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem P2M_QEC_Coding_HypergraphProduct_wordLinearMapTranspose_toLin__eq_8ae563e58468
    {F : Type v} {row col : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype row] [DecidableEq row]
    [Fintype col] [DecidableEq col]
    (M : Matrix row col F) :
    wordLinearMapTranspose (Matrix.toLin' M) = Matrix.toLin' M.transpose := by sorry

alias «QEC».«Coding».«HypergraphProduct».«wordLinearMapTranspose_toLin'_eq» := P2M_QEC_Coding_HypergraphProduct_wordLinearMapTranspose_toLin__eq_8ae563e58468
