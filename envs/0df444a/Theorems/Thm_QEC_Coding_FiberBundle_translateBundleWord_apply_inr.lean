-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_translateBundleWord_apply_inr
-- name    : QEC.Coding.FiberBundle.translateBundleWord_apply_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:44:09.472505+00:00
-- url     : https://prove2.me/theorems/f682afa4-d929-4c17-8a6e-a2349e81a99f
-- title:
--   Fiber Bundle: translate Bundle Word apply inr
-- statement:
--   The Fiber Bundle construction uses the translate Bundle Word apply inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4489-L4498
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4489-L4498

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.translateBundleWord_apply_inr
    {baseZero baseOne : Type u}
    (n : Nat) [NeZero n] (t : ZMod n)
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne (ZMod n) (ZMod n)))
    (a : baseZero) (j : ZMod n) :
    translateBundleWord n t z (Sum.inr (a, j)) =
      z (Sum.inr (a, j - t)) := by sorry
