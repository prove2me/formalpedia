-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_inputDistanceMinimum_le_first
-- name    : QEC.Coding.HypergraphProduct.inputDistanceMinimum_le_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:39:05.751963+00:00
-- url     : https://prove2.me/theorems/fec6d5c4-3604-4097-ad52-9ab6c53dd379
-- title:
--   Hypergraph Product: input Distance Minimum le first
-- statement:
--   The Hypergraph Product construction uses the input Distance Minimum le first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/LowerBound.lean#L32-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/LowerBound.lean#L32-L40

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Duality
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u

theorem QEC.Coding.HypergraphProduct.inputDistanceMinimum_le_first
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    inputDistanceMinimum D ≤ extendedMinimumDistance (firstCode D) := by sorry
