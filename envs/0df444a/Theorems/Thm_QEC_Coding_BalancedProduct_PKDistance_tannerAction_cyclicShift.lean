-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_tannerAction_cyclicShift
-- name    : QEC.Coding.BalancedProduct.PKDistance.tannerAction_cyclicShift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:59:43.249449+00:00
-- url     : https://prove2.me/theorems/0fcc92fd-40e3-46c4-ab29-79208f186332
-- title:
--   PKDistance: tanner Action cyclic Shift
-- statement:
--   Over a commutative balancing group, the lifted Tanner block commutes with
--   every cyclic translation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L609-L640
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L609-L640

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

theorem QEC.Coding.BalancedProduct.PKDistance.tannerAction_cyclicShift
    {G aRow aCol : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    (t : G) (z : Word (ZMod 2) (aCol × G)) :
    tannerAction A (cyclicShift t z) =
      cyclicShift t (tannerAction A z) := by sorry
