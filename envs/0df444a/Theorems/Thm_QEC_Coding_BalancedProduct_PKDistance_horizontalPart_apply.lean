-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_horizontalPart_apply
-- name    : QEC.Coding.BalancedProduct.PKDistance.horizontalPart_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:58:43.281243+00:00
-- url     : https://prove2.me/theorems/0e3a2c1f-b7ac-4e21-8030-8b9779b953f7
-- title:
--   PKDistance: horizontal Part apply
-- statement:
--   The PKDistance construction uses the horizontal Part apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L678-L683
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L678-L683

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

theorem QEC.Coding.BalancedProduct.PKDistance.horizontalPart_apply
    {G aRow aCol : Type}
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (c : aCol) (g : G) :
    horizontalPart z (c, g) = z (Sum.inl (c, (), g)) := by sorry

attribute [defeq] QEC.Coding.BalancedProduct.PKDistance.horizontalPart_apply
