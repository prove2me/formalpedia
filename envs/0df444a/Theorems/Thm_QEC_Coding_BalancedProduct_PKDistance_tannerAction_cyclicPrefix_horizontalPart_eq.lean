-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_tannerAction_cyclicPrefix_horizontalPart_eq
-- name    : QEC.Coding.BalancedProduct.PKDistance.tannerAction_cyclicPrefix_horizontalPart_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:04:55.140191+00:00
-- url     : https://prove2.me/theorems/f66ff62b-d758-49bd-a2a6-8fdfe7ef8435
-- title:
--   PKDistance: tanner Action cyclic Prefix horizontal Part eq
-- statement:
--   For every prefix `u^(t)` of the horizontal part of a concrete cycle,
--   the Tanner syndrome is the cyclic endpoint difference `(1+x^t)v` from PK20
--   Proposition 2, Case 1.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1504-L1518
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1504-L1518

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

theorem QEC.Coding.BalancedProduct.PKDistance.tannerAction_cyclicPrefix_horizontalPart_eq
    {G aRow aCol : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (hz : LiftedProduct.boundary1
      (Cyclic.liftedProductData A x) z = 0)
    (t : Nat) :
    tannerAction A (cyclicPrefix x t (horizontalPart z)) =
      verticalPart z + cyclicShift (x ^ t) (verticalPart z) := by sorry
