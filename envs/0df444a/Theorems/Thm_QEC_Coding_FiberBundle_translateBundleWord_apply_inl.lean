-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_translateBundleWord_apply_inl
-- name    : QEC.Coding.FiberBundle.translateBundleWord_apply_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:43:33.604499+00:00
-- url     : https://prove2.me/theorems/20453a95-7b83-413b-81fb-df76ad4bbf63
-- title:
--   Fiber Bundle: translate Bundle Word apply inl
-- statement:
--   The Fiber Bundle construction uses the translate Bundle Word apply inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4477-L4486
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4477-L4486

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.translateBundleWord_apply_inl
    {baseZero baseOne : Type u}
    (n : Nat) [NeZero n] (t : ZMod n)
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne (ZMod n) (ZMod n)))
    (b : baseOne) (i : ZMod n) :
    translateBundleWord n t z (Sum.inl (b, i)) =
      z (Sum.inl (b, i - t)) := by sorry
