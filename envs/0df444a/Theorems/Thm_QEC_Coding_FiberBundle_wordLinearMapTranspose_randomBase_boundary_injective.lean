-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_wordLinearMapTranspose_randomBase_boundary_injective
-- name    : QEC.Coding.FiberBundle.wordLinearMapTranspose_randomBase_boundary_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:31:23.407494+00:00
-- url     : https://prove2.me/theorems/16bbc69c-e6f8-4d12-b033-336791883647
-- title:
--   Fiber Bundle: word Linear Map Transpose random Base boundary injective
-- statement:
--   Full row rank of the base boundary makes its transpose injective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/CohomologyDimension.lean#L83-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/CohomologyDimension.lean#L83-L101

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_CohomologyDimension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.wordLinearMapTranspose_randomBase_boundary_injective
    {r : Nat} (baseSample : RandomBase.Sample r)
    (hRank : RandomBase.HasFullRowRank baseSample) :
    Function.Injective
      (wordLinearMapTranspose
        (Matrix.toLin' (RandomBase.boundary baseSample))) := by sorry
