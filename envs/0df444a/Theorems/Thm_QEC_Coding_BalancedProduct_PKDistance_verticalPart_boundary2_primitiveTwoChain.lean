-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_verticalPart_boundary2_primitiveTwoChain
-- name    : QEC.Coding.BalancedProduct.PKDistance.verticalPart_boundary2_primitiveTwoChain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:03:20.60911+00:00
-- url     : https://prove2.me/theorems/0c86033d-909a-4d98-abaf-12c54b330438
-- title:
--   PKDistance: vertical Part boundary2 primitive Two Chain
-- statement:
--   The vertical block of the same actual boundary is the Tanner action
--   `A h`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L846-L862
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L846-L862

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

theorem QEC.Coding.BalancedProduct.PKDistance.verticalPart_boundary2_primitiveTwoChain
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (h : Word (ZMod 2) (aCol × G)) :
    verticalPart
        (LiftedProduct.boundary2 (Cyclic.liftedProductData A x)
          (primitiveTwoChain h)) =
      tannerAction A h := by sorry
