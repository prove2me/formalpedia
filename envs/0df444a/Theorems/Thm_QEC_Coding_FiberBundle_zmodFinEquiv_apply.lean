-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_zmodFinEquiv_apply
-- name    : QEC.Coding.FiberBundle.zmodFinEquiv_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:06:43.526083+00:00
-- url     : https://prove2.me/theorems/eba6df72-f7f9-4599-a1dc-36520ec92353
-- title:
--   Fiber Bundle: zmod Fin Equiv apply
-- statement:
--   The standard finite representative is the corresponding natural cast.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L19-L26
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L19-L26

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.zmodFinEquiv_apply
    (n : Nat) [NeZero n] (k : Fin n) :
    ZMod.finEquiv n k = (k.val : ZMod n) := by sorry
