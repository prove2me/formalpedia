-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_precomp_equiv
-- name    : QEC.Coding.BalancedProduct.PKDistance.HammingWeight_precomp_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:58:46.197464+00:00
-- url     : https://prove2.me/theorems/b0fde7a4-8945-4940-93fc-eec3eb299a28
-- title:
--   PKDistance: Hamming Weight precomp equiv
-- statement:
--   Hamming weight is invariant under a bijective reindexing of coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L24-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L24-L36

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

theorem QEC.Coding.BalancedProduct.PKDistance.HammingWeight_precomp_equiv
    {F : Type u} [Zero F] [DecidableEq F]
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (z : Word F ι) :
    HammingWeight (fun k => z (e k)) = HammingWeight z := by sorry
