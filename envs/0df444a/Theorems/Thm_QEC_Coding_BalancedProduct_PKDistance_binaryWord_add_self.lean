-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_binaryWord_add_self
-- name    : QEC.Coding.BalancedProduct.PKDistance.binaryWord_add_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:58:15.749381+00:00
-- url     : https://prove2.me/theorems/fb24e866-158b-4db1-811f-8ade11f04a07
-- title:
--   PKDistance: binary Word add self
-- statement:
--   A binary word added to itself vanishes coordinatewise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L395-L403
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L395-L403

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

theorem QEC.Coding.BalancedProduct.PKDistance.binaryWord_add_self
    {ι : Type u} (z : Word (ZMod 2) ι) : z + z = 0 := by sorry
