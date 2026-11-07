-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_boundary1_eq_tannerAction_add_cyclicDifference
-- name    : QEC.Coding.BalancedProduct.PKDistance.boundary1_eq_tannerAction_add_cyclicDifference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:03:08.409993+00:00
-- url     : https://prove2.me/theorems/55c34828-940b-4d51-b772-2afb77f355e2
-- title:
--   PKDistance: boundary1 eq tanner Action add cyclic Difference
-- statement:
--   Coordinatewise decomposition of the concrete cyclic lifted-product
--   boundary into the Tanner action on the horizontal block and `1+x` on the
--   vertical block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L751-L775
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L751-L775

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

theorem QEC.Coding.BalancedProduct.PKDistance.boundary1_eq_tannerAction_add_cyclicDifference
    {G aRow aCol : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (r : aRow) (go : G) :
    LiftedProduct.boundary1 (Cyclic.liftedProductData A x) z
        (r, (), go) =
      tannerAction A (horizontalPart z) (r, go) +
        (verticalPart z + cyclicShift x (verticalPart z)) (r, go) := by sorry
