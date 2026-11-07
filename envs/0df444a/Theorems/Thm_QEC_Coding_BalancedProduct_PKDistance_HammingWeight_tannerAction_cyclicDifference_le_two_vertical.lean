-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_tannerAction_cyclicDifference_le_two_vertical
-- name    : QEC.Coding.BalancedProduct.PKDistance.HammingWeight_tannerAction_cyclicDifference_le_two_vertical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:00:50.38877+00:00
-- url     : https://prove2.me/theorems/02e520ba-d027-4219-a752-1894f53bec73
-- title:
--   PKDistance: Hamming Weight tanner Action cyclic Difference le two vertical
-- statement:
--   Weight form of the preceding cancellation, matching PK20 Proposition 2,
--   Case 2, equation `|(1+x^t)Ah| <= 2|v|`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1273-L1288
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1273-L1288

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

theorem QEC.Coding.BalancedProduct.PKDistance.HammingWeight_tannerAction_cyclicDifference_le_two_vertical
    {G aRow aCol : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (hz : LiftedProduct.boundary1 (Cyclic.liftedProductData A x) z = 0)
    (h : Word (ZMod 2) (aCol × G))
    (hu : horizontalPart z = h + cyclicShift x h)
    (t : Nat) :
    HammingWeight (tannerAction A (h + cyclicShift (x ^ t) h)) ≤
        2 * HammingWeight (verticalPart z) := by sorry
