-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_supportWord_mem_code_eventMass_large_le
-- name    : QEC.Coding.FiberBundle.RandomBase.supportWord_mem_code_eventMass_large_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:09:02.997597+00:00
-- url     : https://prove2.me/theorems/bf0284b5-0dac-4431-84ad-2b6fd05614b7
-- title:
--   Random Base: support Word mem code event Mass large le
-- statement:
--   Uniform fixed-support estimate once `p |A| ≥ 1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L627-L659
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L627-L659

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.supportWord_mem_code_eventMass_large_le
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r)
    (A : Finset (Fin (4 * r))) (hlarge : 4 * r ≤ A.card * Delta) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => supportWord A ∈ (code sample).carrier) ≤
      (ENNReal.ofReal ((4 : Real) / 7)) ^ (3 * r) := by sorry
