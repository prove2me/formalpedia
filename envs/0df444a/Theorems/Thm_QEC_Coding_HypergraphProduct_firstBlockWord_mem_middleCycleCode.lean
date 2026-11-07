-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_firstBlockWord_mem_middleCycleCode
-- name    : QEC.Coding.HypergraphProduct.firstBlockWord_mem_middleCycleCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:13:23.796494+00:00
-- url     : https://prove2.me/theorems/59072b11-e4f4-4fee-8621-f8c704ce81e2
-- title:
--   Hypergraph Product: first Block Word mem middle Cycle Code
-- statement:
--   A first-block product is a cycle when its first factor is in the first
--   primal code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L249-L277
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L249-L277

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.firstBlockWord_mem_middleCycleCode
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (x : Word F colOne) (y : Word F colTwo)
    (hx : x ∈ (firstCode D).carrier) :
    firstBlockWord (rowOne := rowOne) (rowTwo := rowTwo) x y ∈
      (chainComplex D).middleCycleCode.carrier := by sorry
