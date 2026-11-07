-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_cycleFiberChainBoundary_eq_zero_implies_constant
-- name    : QEC.Coding.FiberBundle.cycleFiberChainBoundary_eq_zero_implies_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:48:53.421967+00:00
-- url     : https://prove2.me/theorems/8d005ed2-cc8e-4f5d-ad49-1133af8b8978
-- title:
--   Fiber Bundle: cycle Fiber Chain Boundary eq zero implies constant
-- statement:
--   A cycle-fiber chain with zero cellular boundary is constant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L433-L445
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L433-L445

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.cycleFiberChainBoundary_eq_zero_implies_constant
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (c : Word (ZMod 2) (ZMod n))
    (hc : cycleFiberChainBoundary n c = 0) :
    ∀ j, c j = c 0 := by sorry
