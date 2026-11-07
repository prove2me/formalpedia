-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_inputDistanceMinimum_le_secondTranspose
-- name    : QEC.Coding.HypergraphProduct.inputDistanceMinimum_le_secondTranspose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:39:29.34493+00:00
-- url     : https://prove2.me/theorems/21fa24ea-b12a-4f6a-b062-efef0820ca76
-- title:
--   Hypergraph Product: input Distance Minimum le second Transpose
-- statement:
--   The Hypergraph Product construction uses the input Distance Minimum le second Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/LowerBound.lean#L63-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/LowerBound.lean#L63-L72

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Duality
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u

theorem QEC.Coding.HypergraphProduct.inputDistanceMinimum_le_secondTranspose
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    inputDistanceMinimum D ≤
      extendedMinimumDistance (secondTransposeCode D) := by sorry
