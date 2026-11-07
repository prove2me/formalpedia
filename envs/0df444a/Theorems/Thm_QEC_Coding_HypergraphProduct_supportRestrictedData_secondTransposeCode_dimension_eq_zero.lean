-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_supportRestrictedData_secondTransposeCode_dimension_eq_zero
-- name    : QEC.Coding.HypergraphProduct.supportRestrictedData_secondTransposeCode_dimension_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:38:00.694876+00:00
-- url     : https://prove2.me/theorems/e5d07da0-47c7-41bf-b193-d89b91334b1d
-- title:
--   Hypergraph Product: support Restricted Data second Transpose Code dimension eq zero
-- statement:
--   Below the second transpose distance, the second restricted transpose code
--   is the zero code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Restriction.lean#L156-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Restriction.lean#L156-L179

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Support
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Restriction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.supportRestrictedData_secondTransposeCode_dimension_eq_zero
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo))
    (hz : (HammingWeight z : WithTop Nat) <
      extendedMinimumDistance (secondTransposeCode D)) :
    Dimension (secondTransposeCode (supportRestrictedData D z)) = 0 := by sorry
