-- Prove2me | Theorems.Thm_P2M_QEC_Coding_HypergraphProduct_finrank_range_toLin__eq_rank_581f87e1a42a
-- name    : P2M_QEC_Coding_HypergraphProduct_finrank_range_toLin__eq_rank_581f87e1a42a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:36:49.764198+00:00
-- url     : https://prove2.me/theorems/9809fb91-2a07-49d1-baaa-63cc57deb155
-- title:
--   P2 M QEC Coding Hypergraph Product finrank range to Lin  eq rank 581f87e1a42a: P2 M QEC Coding Hypergraph Product finrank range to Lin  eq rank 581f87e1a42a
-- statement:
--   Matrix rank is the finrank of the range of its coordinate word map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/Formula.lean#L172-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/Formula.lean#L172-L178

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_BoundaryMaps
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Formula
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem P2M_QEC_Coding_HypergraphProduct_finrank_range_toLin__eq_rank_581f87e1a42a
    {F : Type v} {row col : Type u}
    [Field F]
    [Fintype row] [Fintype col] [DecidableEq col]
    (M : Matrix row col F) :
    Module.finrank F (LinearMap.range (Matrix.toLin' M)) = M.rank := by sorry

alias «QEC».«Coding».«HypergraphProduct».«finrank_range_toLin'_eq_rank» := P2M_QEC_Coding_HypergraphProduct_finrank_range_toLin__eq_rank_581f87e1a42a
