-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_boundary1TransposeTensorMap_eq_joint
-- name    : QEC.Coding.HypergraphProduct.boundary1TransposeTensorMap_eq_joint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:35:36.942823+00:00
-- url     : https://prove2.me/theorems/1f861d68-f2ec-49f2-a158-bdad0ccab11b
-- title:
--   Hypergraph Product: boundary1 Transpose Tensor Map eq joint
-- statement:
--   The Hypergraph Product construction uses the boundary1 Transpose Tensor Map eq joint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/BoundaryMaps.lean#L144-L192
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/BoundaryMaps.lean#L144-L192

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Realization
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_BoundaryMaps
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
open TensorProduct

theorem QEC.Coding.HypergraphProduct.boundary1TransposeTensorMap_eq_joint
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    boundary1TransposeTensorMap D =
      jointTensorWordMap (Matrix.toLin' D.first.transpose)
        (Matrix.toLin' D.second) := by sorry
