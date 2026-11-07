-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_fibreWeight_cyclicShift
-- name    : QEC.Coding.BalancedProduct.PKDistance.fibreWeight_cyclicShift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:01:52.782302+00:00
-- url     : https://prove2.me/theorems/0dd1eb8a-4162-4274-bcf5-02ae30206c08
-- title:
--   PKDistance: fibre Weight cyclic Shift
-- statement:
--   Translation in the cyclic coordinate preserves each individual fibre
--   weight, not only the total word weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L134-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L134-L139

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

theorem QEC.Coding.BalancedProduct.PKDistance.fibreWeight_cyclicShift
    {I : Type u} {G : Type v} [Group G] [Fintype G]
    (t : G) (z : Word (ZMod 2) (I × G)) (i : I) :
    fibreWeight (cyclicShift t z) i = fibreWeight z i := by sorry
