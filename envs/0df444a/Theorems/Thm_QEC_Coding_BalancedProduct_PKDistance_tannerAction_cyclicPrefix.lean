-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_tannerAction_cyclicPrefix
-- name    : QEC.Coding.BalancedProduct.PKDistance.tannerAction_cyclicPrefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:02:59.636338+00:00
-- url     : https://prove2.me/theorems/87c6d917-abb1-4c5f-a764-0ddfd989d7e0
-- title:
--   PKDistance: tanner Action cyclic Prefix
-- statement:
--   The Tanner action commutes with every finite cyclic polynomial prefix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L643-L655
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L643-L655

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

theorem QEC.Coding.BalancedProduct.PKDistance.tannerAction_cyclicPrefix
    {G aRow aCol : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    (x : G) (t : Nat) (z : Word (ZMod 2) (aCol × G)) :
    tannerAction A (cyclicPrefix x t z) =
      cyclicPrefix x t (tannerAction A z) := by sorry
