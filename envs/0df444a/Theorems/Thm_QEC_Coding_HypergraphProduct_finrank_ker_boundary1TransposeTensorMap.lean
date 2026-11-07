-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_finrank_ker_boundary1TransposeTensorMap
-- name    : QEC.Coding.HypergraphProduct.finrank_ker_boundary1TransposeTensorMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:36:27.225374+00:00
-- url     : https://prove2.me/theorems/207f754a-038b-43c4-9dea-9b1f66cc93db
-- title:
--   Hypergraph Product: finrank ker boundary1 Transpose Tensor Map
-- statement:
--   The Hypergraph Product construction uses the finrank ker boundary1 Transpose Tensor Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/Formula.lean#L56-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/Formula.lean#L56-L71

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_BoundaryMaps
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Formula
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.finrank_ker_boundary1TransposeTensorMap
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    Module.finrank (ZMod 2) (LinearMap.ker (boundary1TransposeTensorMap D)) =
      Module.finrank (ZMod 2)
        (LinearMap.ker (wordLinearMapTranspose (boundary1 D))) := by sorry
