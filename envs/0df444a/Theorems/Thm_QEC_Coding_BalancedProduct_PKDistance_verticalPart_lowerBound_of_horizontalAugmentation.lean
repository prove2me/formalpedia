-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_verticalPart_lowerBound_of_horizontalAugmentation
-- name    : QEC.Coding.BalancedProduct.PKDistance.verticalPart_lowerBound_of_horizontalAugmentation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:01:21.277813+00:00
-- url     : https://prove2.me/theorems/55ef24f6-d46d-459c-bc65-eb7680390367
-- title:
--   PKDistance: vertical Part lower Bound of horizontal Augmentation
-- statement:
--   Canonical-cycle form of the Case-1 expansion bound.  The full-prefix
--   endpoint has been eliminated in favor of the actual horizontal augmentation
--   of the lifted-product cycle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L2098-L2125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L2098-L2125

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

theorem QEC.Coding.BalancedProduct.PKDistance.verticalPart_lowerBound_of_horizontalAugmentation
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : LiftedProduct.boundary1
      (Cyclic.data q A) z = 0)
    (threshold stepBound expansionNumerator expansionDenominator : Nat)
    (hthreshold : 0 < threshold)
    (haugmentation : threshold ≤ q * HammingWeight
      (HorizontalSubsystem.horizontalAugmentation z))
    (hstepBound : HammingWeight (horizontalPart z) ≤ stepBound)
    (hExpansion : (tannerAction A).SmallSetExpanding
      threshold expansionNumerator expansionDenominator) :
    expansionNumerator * (threshold - stepBound) ≤
      2 * expansionDenominator * HammingWeight (verticalPart z) := by sorry
