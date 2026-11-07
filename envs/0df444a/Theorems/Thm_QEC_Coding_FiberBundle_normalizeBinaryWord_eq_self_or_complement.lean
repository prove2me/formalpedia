-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_normalizeBinaryWord_eq_self_or_complement
-- name    : QEC.Coding.FiberBundle.normalizeBinaryWord_eq_self_or_complement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:19:54.704597+00:00
-- url     : https://prove2.me/theorems/1a0e7de7-9040-4d00-ba47-ca91c8fb921c
-- title:
--   Fiber Bundle: normalize Binary Word eq self or complement
-- statement:
--   Normalization either keeps the word or toggles it by the all-one word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L403-L409
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L403-L409

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.normalizeBinaryWord_eq_self_or_complement
    {ι : Type u} [Fintype ι] (x : Word (ZMod 2) ι) :
    normalizeBinaryWord x = x ∨ normalizeBinaryWord x = binaryComplement x := by sorry
