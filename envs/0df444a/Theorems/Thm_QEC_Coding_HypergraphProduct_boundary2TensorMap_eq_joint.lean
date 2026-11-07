-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_boundary2TensorMap_eq_joint
-- name    : QEC.Coding.HypergraphProduct.boundary2TensorMap_eq_joint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:35:40.551147+00:00
-- url     : https://prove2.me/theorems/cf64acfd-924a-4e02-9104-42d6e97616b7
-- title:
--   Hypergraph Product: boundary2 Tensor Map eq joint
-- statement:
--   The Hypergraph Product construction uses the boundary2 Tensor Map eq joint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/BoundaryMaps.lean#L194-L242
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/BoundaryMaps.lean#L194-L242

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Realization
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_BoundaryMaps
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
open TensorProduct

theorem QEC.Coding.HypergraphProduct.boundary2TensorMap_eq_joint
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    boundary2TensorMap D =
      jointTensorWordMap (Matrix.toLin' D.first)
        (Matrix.toLin' D.second.transpose) := by sorry
