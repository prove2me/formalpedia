-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_supportWord_mem_code_eventMass_small_geometric_le
-- name    : QEC.Coding.FiberBundle.RandomBase.supportWord_mem_code_eventMass_small_geometric_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:05:54.076328+00:00
-- url     : https://prove2.me/theorems/aed0eef2-1e3a-4fad-a1ce-35ceea3e5d40
-- title:
--   Random Base: support Word mem code event Mass small geometric le
-- statement:
--   For supports below the correlation length `4r / Delta`, substituting
--   `p = Delta/(4r)` turns the fixed-support probability into a geometric weight
--   `exp(-3 Delta / 8)^|A|`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L370-L424
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L370-L424

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.supportWord_mem_code_eventMass_small_geometric_le
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r)
    (A : Finset (Fin (4 * r))) (hsmall : A.card * Delta ≤ 4 * r) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => supportWord A ∈ (code sample).carrier) ≤
      (ENNReal.ofReal
        (Real.exp (-(3 : Real) * Delta / 8))) ^ A.card := by sorry
