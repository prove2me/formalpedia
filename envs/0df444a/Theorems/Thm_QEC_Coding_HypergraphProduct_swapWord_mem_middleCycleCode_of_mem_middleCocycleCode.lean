-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_swapWord_mem_middleCycleCode_of_mem_middleCocycleCode
-- name    : QEC.Coding.HypergraphProduct.swapWord_mem_middleCycleCode_of_mem_middleCocycleCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:39:10.250227+00:00
-- url     : https://prove2.me/theorems/b5109c16-efd2-4b8c-9f50-5dabdad10b92
-- title:
--   Hypergraph Product: swap Word mem middle Cycle Code of mem middle Cocycle Code
-- statement:
--   An original cocycle becomes a cycle for the transposed input data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Duality.lean#L138-L150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Duality.lean#L138-L150

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Duality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.swapWord_mem_middleCycleCode_of_mem_middleCocycleCode
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo))
    (hz : z ∈ (chainComplex D).middleCocycleCode.carrier) :
    swapWord z ∈ (chainComplex (transposeData D)).middleCycleCode.carrier := by sorry
