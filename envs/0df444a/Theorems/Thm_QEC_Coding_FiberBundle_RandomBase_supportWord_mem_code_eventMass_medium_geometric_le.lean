-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_supportWord_mem_code_eventMass_medium_geometric_le
-- name    : QEC.Coding.FiberBundle.RandomBase.supportWord_mem_code_eventMass_medium_geometric_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:43:37.955808+00:00
-- url     : https://prove2.me/theorems/6cb4556f-e6c6-4d9e-be7c-0ca862b94116
-- title:
--   Random Base: support Word mem code event Mass medium geometric le
-- statement:
--   Fixed-support geometric estimate throughout the enlarged regime
--   `Delta |A| ≤ 12r`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L530-L588
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L530-L588

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.supportWord_mem_code_eventMass_medium_geometric_le
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r)
    (A : Finset (Fin (4 * r))) (hmedium : A.card * Delta ≤ 12 * r) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => supportWord A ∈ (code sample).carrier) ≤
      (ENNReal.ofReal
        (Real.exp (-(3 : Real) * Delta / 28))) ^ A.card := by sorry
