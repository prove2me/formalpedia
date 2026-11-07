-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_verticalPart_lowerBound_of_nonzero_horizontalClass_invGenerator
-- name    : QEC.Coding.BalancedProduct.PKDistance.verticalPart_lowerBound_of_nonzero_horizontalClass_invGenerator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:06:20.502587+00:00
-- url     : https://prove2.me/theorems/7aef98c2-ba92-4b9b-ab5b-6835aaf1a4a7
-- title:
--   PKDistance: vertical Part lower Bound of nonzero horizontal Class inv Generator
-- statement:
--   PK20 Case 1 with its endpoint discharged in the inverse cyclic
--   orientation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L2204-L2248
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L2204-L2248

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

theorem QEC.Coding.BalancedProduct.PKDistance.verticalPart_lowerBound_of_nonzero_horizontalClass_invGenerator
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData A
        (Cyclic.cyclicGenerator q)⁻¹)).middleCycleCode.carrier)
    {d : Nat}
    (hMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex A).middleCycleCode d)
    (hProjected : HorizontalSubsystem.horizontalHomologyProjection A
      (Cyclic.cyclicGenerator q)⁻¹
      ((LiftedProduct.chainComplex
        (Cyclic.liftedProductData A
          (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryInCycles.mkQ
            ⟨z, hz⟩) ≠ 0)
    (stepBound expansionNumerator expansionDenominator : Nat)
    (hd : 0 < d)
    (hstepBound : HammingWeight (horizontalPart z) ≤ stepBound)
    (hExpansion : (tannerAction A).SmallSetExpanding
      (q * d) expansionNumerator expansionDenominator) :
    expansionNumerator * (q * d - stepBound) ≤
      2 * expansionDenominator * HammingWeight (verticalPart z) := by sorry
