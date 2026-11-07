-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_fibreSum_horizontalPart_eq_horizontalAugmentation
-- name    : QEC.Coding.BalancedProduct.PKDistance.fibreSum_horizontalPart_eq_horizontalAugmentation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:59:35.375355+00:00
-- url     : https://prove2.me/theorems/1ef5075f-cdbd-4570-b896-3654a4a3e0fc
-- title:
--   PKDistance: fibre Sum horizontal Part eq horizontal Augmentation
-- statement:
--   The PKDistance construction uses the fibre Sum horizontal Part eq horizontal Augmentation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1794-L1801
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1794-L1801

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

theorem QEC.Coding.BalancedProduct.PKDistance.fibreSum_horizontalPart_eq_horizontalAugmentation
    {G aRow aCol : Type} [Fintype G]
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G)) :
    fibreSum (horizontalPart z) =
      HorizontalSubsystem.horizontalAugmentation z := by sorry
