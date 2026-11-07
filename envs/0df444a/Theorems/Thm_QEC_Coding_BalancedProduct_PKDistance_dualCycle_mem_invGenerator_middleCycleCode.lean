-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_dualCycle_mem_invGenerator_middleCycleCode
-- name    : QEC.Coding.BalancedProduct.PKDistance.dualCycle_mem_invGenerator_middleCycleCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:59:39.522129+00:00
-- url     : https://prove2.me/theorems/aadf6ba2-b4a6-4c5e-ba37-a77f125747ba
-- title:
--   PKDistance: dual Cycle mem inv Generator middle Cycle Code
-- statement:
--   The exchanged cocycle is a cycle in the explicit inverse-generator
--   normal form of the dual lifted product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L2474-L2498
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L2474-L2498

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w

theorem QEC.Coding.BalancedProduct.PKDistance.dualCycle_mem_invGenerator_middleCycleCode
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleCocycleCode.carrier) :
    LiftedProductDuality.swapWord z ∈
      (LiftedProduct.chainComplex
        (Cyclic.liftedProductData (LiftedProduct.starTranspose A)
          (Cyclic.cyclicGenerator q)⁻¹)).middleCycleCode.carrier := by sorry
