-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_swapWord_mem_middleCycleCode_of_mem_middleCocycleCode
-- name    : QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_mem_middleCycleCode_of_mem_middleCocycleCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:39:24.763977+00:00
-- url     : https://prove2.me/theorems/f84db3f9-5bca-4664-a295-6226070b18eb
-- title:
--   Lifted Product Duality: swap Word mem middle Cycle Code of mem middle Cocycle Code
-- statement:
--   An original cocycle becomes a cycle for the dual lifted-product data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LiftedProductDuality.lean#L215-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LiftedProductDuality.lean#L215-L230

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LiftedProductDuality
open QEC.Coding
universe u v

theorem QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_mem_middleCycleCode_of_mem_middleCocycleCode
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : LiftedProduct.Data (ZMod 2) G aRow aCol bRow bCol)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol bRow bCol G))
    (hz : z ∈ (LiftedProduct.chainComplex D).middleCocycleCode.carrier) :
    swapWord z ∈
      (LiftedProduct.chainComplex (dualData D)).middleCycleCode.carrier := by sorry
