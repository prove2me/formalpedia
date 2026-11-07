-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_verticalPart_lowerBound_of_cyclicPrefix_crossing
-- name    : QEC.Coding.BalancedProduct.PKDistance.verticalPart_lowerBound_of_cyclicPrefix_crossing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:01:02.029272+00:00
-- url     : https://prove2.me/theorems/e83bbc23-287e-4696-8104-add5aebcc9a0
-- title:
--   PKDistance: vertical Part lower Bound of cyclic Prefix crossing
-- statement:
--   Quantitative core of PK20 Proposition 2, Case 1.  Once a cyclic prefix of
--   the concrete horizontal block crosses `threshold`, small-set expansion forces
--   the concrete vertical block to be large.  The endpoint-crossing premise is
--   later discharged from the nonzero quotient Tanner class and its distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1524-L1581
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1524-L1581

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

theorem QEC.Coding.BalancedProduct.PKDistance.verticalPart_lowerBound_of_cyclicPrefix_crossing
    {G aRow aCol : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (hz : LiftedProduct.boundary1
      (Cyclic.liftedProductData A x) z = 0)
    (last threshold stepBound expansionNumerator expansionDenominator : Nat)
    (hthreshold : 0 < threshold)
    (hend : threshold ≤
      HammingWeight (cyclicPrefix x last (horizontalPart z)))
    (hstepBound : HammingWeight (horizontalPart z) ≤ stepBound)
    (hExpansion : (tannerAction A).SmallSetExpanding
      threshold expansionNumerator expansionDenominator) :
    expansionNumerator * (threshold - stepBound) ≤
      2 * expansionDenominator * HammingWeight (verticalPart z) := by sorry
