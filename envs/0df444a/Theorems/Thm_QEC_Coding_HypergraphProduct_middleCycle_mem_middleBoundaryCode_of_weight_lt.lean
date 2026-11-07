-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_middleCycle_mem_middleBoundaryCode_of_weight_lt
-- name    : QEC.Coding.HypergraphProduct.middleCycle_mem_middleBoundaryCode_of_weight_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:33:32.926499+00:00
-- url     : https://prove2.me/theorems/4f5144c0-2087-4c32-9607-10728907c049
-- title:
--   Hypergraph Product: middle Cycle mem middle Boundary Code of weight lt
-- statement:
--   A homological logical word cannot have weight below both the first primal
--   distance and the second transpose distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Embedding.lean#L248-L288
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Embedding.lean#L248-L288

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Restriction
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.middleCycle_mem_middleBoundaryCode_of_weight_lt
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo))
    (hzCycle : z ∈ (chainComplex D).middleCycleCode.carrier)
    (hzFirst : (HammingWeight z : WithTop Nat) <
      extendedMinimumDistance (firstCode D))
    (hzSecondTranspose : (HammingWeight z : WithTop Nat) <
      extendedMinimumDistance (secondTransposeCode D)) :
    z ∈ (chainComplex D).middleBoundaryCode.carrier := by sorry
