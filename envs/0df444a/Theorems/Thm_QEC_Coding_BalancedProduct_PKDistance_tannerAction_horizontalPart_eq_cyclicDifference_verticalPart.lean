-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_tannerAction_horizontalPart_eq_cyclicDifference_verticalPart
-- name    : QEC.Coding.BalancedProduct.PKDistance.tannerAction_horizontalPart_eq_cyclicDifference_verticalPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:00:40.592201+00:00
-- url     : https://prove2.me/theorems/b0b7419b-1a6b-406e-bc71-61131c38f38c
-- title:
--   PKDistance: tanner Action horizontal Part eq cyclic Difference vertical Part
-- statement:
--   A concrete lifted-product cycle satisfies the PK20 cycle equation
--   `A u = (1+x)v`; the equation is derived from `boundary1 z = 0`, not supplied
--   as a theorem field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L780-L810
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L780-L810

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

theorem QEC.Coding.BalancedProduct.PKDistance.tannerAction_horizontalPart_eq_cyclicDifference_verticalPart
    {G aRow aCol : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (hz : LiftedProduct.boundary1
      (Cyclic.liftedProductData A x) z = 0) :
    tannerAction A (horizontalPart z) =
      verticalPart z + cyclicShift x (verticalPart z) := by sorry
