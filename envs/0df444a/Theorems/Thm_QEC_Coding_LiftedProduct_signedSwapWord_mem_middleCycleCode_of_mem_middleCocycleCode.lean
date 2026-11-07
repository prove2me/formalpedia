-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_mem_middleCycleCode_of_mem_middleCocycleCode
-- name    : QEC.Coding.LiftedProduct.signedSwapWord_mem_middleCycleCode_of_mem_middleCocycleCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:13:25.365499+00:00
-- url     : https://prove2.me/theorems/190ca6f3-4e36-4432-90c2-7dbc6cc18b23
-- title:
--   Lifted Product: signed Swap Word mem middle Cycle Code of mem middle Cocycle Code
-- statement:
--   An original cocycle becomes a cycle for the signed dual lifted product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProductDuality.lean#L230-L245
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProductDuality.lean#L230-L245

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.signedSwapWord_mem_middleCycleCode_of_mem_middleCocycleCode
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [DecidableEq F]
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (z : Word F (QubitIndex aRow aCol bRow bCol G))
    (hz : z ∈ (chainComplex D).middleCocycleCode.carrier) :
    signedSwapWord z ∈
      (chainComplex (dualData D)).middleCycleCode.carrier := by sorry
