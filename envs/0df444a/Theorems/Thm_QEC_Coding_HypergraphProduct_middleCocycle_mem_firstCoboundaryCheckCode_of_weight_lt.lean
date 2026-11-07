-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_middleCocycle_mem_firstCoboundaryCheckCode_of_weight_lt
-- name    : QEC.Coding.HypergraphProduct.middleCocycle_mem_firstCoboundaryCheckCode_of_weight_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:38:39.727617+00:00
-- url     : https://prove2.me/theorems/e69b95df-b2da-4a25-8a8b-e175234a6153
-- title:
--   Hypergraph Product: middle Cocycle mem first Coboundary Check Code of weight lt
-- statement:
--   A cohomological logical word cannot have weight below both the second
--   primal distance and the first transpose distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Duality.lean#L180-L208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Duality.lean#L180-L208

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Duality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.middleCocycle_mem_firstCoboundaryCheckCode_of_weight_lt
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo))
    (hzCocycle : z ∈ (chainComplex D).middleCocycleCode.carrier)
    (hzSecond : (HammingWeight z : WithTop Nat) <
      extendedMinimumDistance (secondCode D))
    (hzFirstTranspose : (HammingWeight z : WithTop Nat) <
      extendedMinimumDistance (firstTransposeCode D)) :
    z ∈ (chainComplex D).firstCoboundaryCheckCode.carrier := by sorry
