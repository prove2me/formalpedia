-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_exists_isHorizontalWeightMinimal
-- name    : QEC.Coding.FiberBundle.exists_isHorizontalWeightMinimal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:57:56.93892+00:00
-- url     : https://prove2.me/theorems/286273a0-e985-4e04-a5a2-0a5d3621da7e
-- title:
--   Fiber Bundle: exists is Horizontal Weight Minimal
-- statement:
--   A horizontal-weight-minimal correction exists because the correction space is finite.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2269-L2297
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2269-L2297

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.exists_isHorizontalWeightMinimal
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r))) :
    ∃ u : Word (ZMod 2)
        (C0Index (Fin (3 * r)) (ZMod (ell * ell))),
      IsHorizontalWeightMinimal baseSample twistSample x u := by sorry
