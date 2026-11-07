-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_cycleFiberCoboundary_eq_zero_implies_constant
-- name    : QEC.Coding.FiberBundle.cycleFiberCoboundary_eq_zero_implies_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:55:27.616414+00:00
-- url     : https://prove2.me/theorems/dbeebfca-5eb2-41b3-b493-6eef6cd4c6dc
-- title:
--   Fiber Bundle: cycle Fiber Coboundary eq zero implies constant
-- statement:
--   A cycle-fiber word with zero coboundary is constant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L271-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L271-L291

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.cycleFiberCoboundary_eq_zero_implies_constant
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (f : Word (ZMod 2) (ZMod n))
    (hf : cycleFiberCoboundary n f = 0) :
    ∀ j, f j = f 0 := by sorry
