-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_firstBlockWord_mem_middleCocycleCode
-- name    : QEC.Coding.HypergraphProduct.firstBlockWord_mem_middleCocycleCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:13:29.699621+00:00
-- url     : https://prove2.me/theorems/f282a925-390d-4279-8973-c3b47cf4a460
-- title:
--   Hypergraph Product: first Block Word mem middle Cocycle Code
-- statement:
--   A first-block product is a cocycle when its second factor is in the second
--   primal code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L281-L308
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L281-L308

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.firstBlockWord_mem_middleCocycleCode
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (x : Word F colOne) (y : Word F colTwo)
    (hy : y ∈ (secondCode D).carrier) :
    firstBlockWord (rowOne := rowOne) (rowTwo := rowTwo) x y ∈
      (chainComplex D).middleCocycleCode.carrier := by sorry
