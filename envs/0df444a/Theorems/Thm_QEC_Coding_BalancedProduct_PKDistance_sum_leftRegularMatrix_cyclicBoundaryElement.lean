-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_sum_leftRegularMatrix_cyclicBoundaryElement
-- name    : QEC.Coding.BalancedProduct.PKDistance.sum_leftRegularMatrix_cyclicBoundaryElement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:01:25.178902+00:00
-- url     : https://prove2.me/theorems/5138b405-dc82-45e2-93db-6c08fb1fc4e5
-- title:
--   PKDistance: sum left Regular Matrix cyclic Boundary Element
-- statement:
--   The left-regular action of the concrete group-algebra element `1+x` is
--   the binary cyclic difference `z + shift x z`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L711-L746
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L711-L746

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

theorem QEC.Coding.BalancedProduct.PKDistance.sum_leftRegularMatrix_cyclicBoundaryElement
    {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G]
    (x : G) (z : Word (ZMod 2) G) (go : G) :
    (∑ gi, LiftedProduct.leftRegularMatrix
        (Cyclic.cyclicBoundaryElement x) go gi * z gi) =
      z go + z (go * x⁻¹) := by sorry
