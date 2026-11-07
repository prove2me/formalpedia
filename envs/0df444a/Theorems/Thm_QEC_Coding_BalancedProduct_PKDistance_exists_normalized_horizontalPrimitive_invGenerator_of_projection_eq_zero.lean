-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_exists_normalized_horizontalPrimitive_invGenerator_of_projection_eq_zero
-- name    : QEC.Coding.BalancedProduct.PKDistance.exists_normalized_horizontalPrimitive_invGenerator_of_projection_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:06:02.679656+00:00
-- url     : https://prove2.me/theorems/9c18efe8-8137-410e-b77f-83907c3fc4fb
-- title:
--   PKDistance: exists normalized horizontal Primitive inv Generator of projection eq zero
-- statement:
--   Zero-horizontal-projection primitive for the inverse generator appearing
--   in the star-transposed lifted product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1833-L1860
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1833-L1860

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

theorem QEC.Coding.BalancedProduct.PKDistance.exists_normalized_horizontalPrimitive_invGenerator_of_projection_eq_zero
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData A
        (Cyclic.cyclicGenerator q)⁻¹)).middleCycleCode.carrier)
    (hProjected : HorizontalSubsystem.horizontalHomologyProjection A
      (Cyclic.cyclicGenerator q)⁻¹
      ((LiftedProduct.chainComplex
        (Cyclic.liftedProductData A
          (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryInCycles.mkQ
            ⟨z, hz⟩) = 0) :
    ∃ h : Word (ZMod 2) (aCol × Cyclic.CyclicGroup q),
      horizontalPart z =
        h + cyclicShift (Cyclic.cyclicGenerator q)⁻¹ h ∧
      ∀ c, 2 * fibreWeight h c ≤ q := by sorry
