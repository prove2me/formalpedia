-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_tannerAction_cyclicDifference_eq_verticalDifference_caseTwo
-- name    : QEC.Coding.BalancedProduct.PKDistance.tannerAction_cyclicDifference_eq_verticalDifference_caseTwo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:04:44.34707+00:00
-- url     : https://prove2.me/theorems/040b7cbc-f294-4060-add4-b0768f771844
-- title:
--   PKDistance: tanner Action cyclic Difference eq vertical Difference case Two
-- statement:
--   In Case 2, the constant cyclic remainder cancels from every translated
--   Tanner difference, leaving exactly the corresponding difference of the
--   concrete vertical block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1223-L1269
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1223-L1269

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

theorem QEC.Coding.BalancedProduct.PKDistance.tannerAction_cyclicDifference_eq_verticalDifference_caseTwo
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
    tannerAction A (h + cyclicShift (x ^ t) h) =
      verticalPart z + cyclicShift (x ^ t) (verticalPart z) := by sorry
