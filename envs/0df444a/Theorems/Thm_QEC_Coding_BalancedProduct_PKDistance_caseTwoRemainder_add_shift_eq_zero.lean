-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_caseTwoRemainder_add_shift_eq_zero
-- name    : QEC.Coding.BalancedProduct.PKDistance.caseTwoRemainder_add_shift_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:59:51.189193+00:00
-- url     : https://prove2.me/theorems/5af03781-26db-4613-9196-197832b7f75a
-- title:
--   PKDistance: case Two Remainder add shift eq zero
-- statement:
--   For a concrete cycle with `u=(1+x)h`, the residual vertical word is
--   invariant under the cyclic generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L878-L904
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L878-L904

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

theorem QEC.Coding.BalancedProduct.PKDistance.caseTwoRemainder_add_shift_eq_zero
    {G aRow aCol : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (hz : LiftedProduct.boundary1
      (Cyclic.liftedProductData A x) z = 0)
    (h : Word (ZMod 2) (aCol × G))
    (hu : horizontalPart z = h + cyclicShift x h) :
    caseTwoRemainder A z h + cyclicShift x (caseTwoRemainder A z h) = 0 := by sorry
