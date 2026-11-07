-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_supportWord_mem_code_eventMass_veryLarge_le
-- name    : QEC.Coding.FiberBundle.RandomBase.supportWord_mem_code_eventMass_veryLarge_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:44:50.016846+00:00
-- url     : https://prove2.me/theorems/4eaf8117-dc5e-40da-8d89-0bd7f8c19d3e
-- title:
--   Random Base: support Word mem code event Mass very Large le
-- statement:
--   Uniform fixed-support estimate in the regime `12r ≤ Delta |A|`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L591-L624
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L591-L624

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.supportWord_mem_code_eventMass_veryLarge_le
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r)
    (A : Finset (Fin (4 * r))) (hlarge : 12 * r ≤ A.card * Delta) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => supportWord A ∈ (code sample).carrier) ≤
      (ENNReal.ofReal ((172 : Real) / 343)) ^ (3 * r) := by sorry
