-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_translateBundleWord_add
-- name    : QEC.Coding.FiberBundle.translateBundleWord_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:54:17.544758+00:00
-- url     : https://prove2.me/theorems/e40080f0-d284-4f03-9603-53c92c8bce2a
-- title:
--   Fiber Bundle: translate Bundle Word add
-- statement:
--   Fiber translations compose by adding their translation parameters.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4659-L4673
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4659-L4673

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.translateBundleWord_add
    {baseZero baseOne : Type u}
    (n : Nat) [NeZero n] (s t : ZMod n)
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne (ZMod n) (ZMod n))) :
    translateBundleWord n s (translateBundleWord n t z) =
      translateBundleWord n (s + t) z := by sorry
