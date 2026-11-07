-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstCoboundaryCheckCode_of_swapWord_mem_middleBoundaryCode
-- name    : QEC.Coding.HypergraphProduct.mem_firstCoboundaryCheckCode_of_swapWord_mem_middleBoundaryCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:38:40.017894+00:00
-- url     : https://prove2.me/theorems/fdb496b0-31b2-4538-96a0-650d0159afb6
-- title:
--   Hypergraph Product: mem first Coboundary Check Code of swap Word mem middle Boundary Code
-- statement:
--   If the exchanged word is a boundary for the transposed data, the original
--   word is a coboundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Duality.lean#L154-L176
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Duality.lean#L154-L176

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Duality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.mem_firstCoboundaryCheckCode_of_swapWord_mem_middleBoundaryCode
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo))
    (hz : swapWord z ∈
      (chainComplex (transposeData D)).middleBoundaryCode.carrier) :
    z ∈ (chainComplex D).firstCoboundaryCheckCode.carrier := by sorry
