-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_secondBlockWord_mem_middleCycleCode
-- name    : QEC.Coding.HypergraphProduct.secondBlockWord_mem_middleCycleCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:13:37.053092+00:00
-- url     : https://prove2.me/theorems/6db7d97e-b714-43a0-b64c-d100e5f356a4
-- title:
--   Hypergraph Product: second Block Word mem middle Cycle Code
-- statement:
--   A second-block product is a cycle when its second factor is in the second
--   transpose code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L312-L345
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L312-L345

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.secondBlockWord_mem_middleCycleCode
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (x : Word F rowOne) (y : Word F rowTwo)
    (hy : y ∈ (secondTransposeCode D).carrier) :
    secondBlockWord (colOne := colOne) (colTwo := colTwo) x y ∈
      (chainComplex D).middleCycleCode.carrier := by sorry
