-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_verticalPart_apply
-- name    : QEC.Coding.BalancedProduct.PKDistance.verticalPart_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:58:21.238193+00:00
-- url     : https://prove2.me/theorems/065acdb3-fe69-4569-b3cb-673ac7e51b53
-- title:
--   PKDistance: vertical Part apply
-- statement:
--   The PKDistance construction uses the vertical Part apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L686-L691
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L686-L691

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

theorem QEC.Coding.BalancedProduct.PKDistance.verticalPart_apply
    {G aRow aCol : Type}
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (r : aRow) (g : G) :
    verticalPart z (r, g) = z (Sum.inr (r, (), g)) := by sorry

attribute [defeq] QEC.Coding.BalancedProduct.PKDistance.verticalPart_apply
