-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_cycleFiberChainBoundary_cycleFiberChainPrimitive
-- name    : QEC.Coding.FiberBundle.cycleFiberChainBoundary_cycleFiberChainPrimitive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:48:51.264196+00:00
-- url     : https://prove2.me/theorems/d8c05abb-84c1-4df8-bd73-ca6fcf5ef4f4
-- title:
--   Fiber Bundle: cycle Fiber Chain Boundary cycle Fiber Chain Primitive
-- statement:
--   Every even-parity cycle zero-chain has the explicit shifted primitive.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L326-L341
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L326-L341

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.cycleFiberChainBoundary_cycleFiberChainPrimitive
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (g : Word (ZMod 2) (ZMod n))
    (hg : (∑ i : ZMod n, g i) = 0) :
    cycleFiberChainBoundary n (cycleFiberChainPrimitive n g) = g := by sorry
