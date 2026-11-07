-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_supportWord_hammingSupport
-- name    : QEC.Coding.FiberBundle.RandomBase.supportWord_hammingSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:39:29.083373+00:00
-- url     : https://prove2.me/theorems/9770a952-301d-4a97-bad5-a1a9301b0abb
-- title:
--   Random Base: support Word hamming Support
-- statement:
--   Every binary word is the indicator of its Hamming support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L267-L275
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L267-L275

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.supportWord_hammingSupport
    {r : Nat} (x : Word (ZMod 2) (Fin (4 * r))) :
    supportWord (hammingSupport x) = x := by sorry
