-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_supportWord_mem_code_eventMass_expEnvelope_le
-- name    : QEC.Coding.FiberBundle.RandomBase.supportWord_mem_code_eventMass_expEnvelope_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:05:58.01228+00:00
-- url     : https://prove2.me/theorems/ab56e207-d252-4b15-b268-e55d7ebbb39b
-- title:
--   Random Base: support Word mem code event Mass exp Envelope le
-- statement:
--   For every fixed support, retain the exponential parity envelope before any
--   large-weight simplification.  This weight dependence is needed for the
--   Gilbert--Varshamov counting range.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L431-L457
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L431-L457

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.supportWord_mem_code_eventMass_expEnvelope_le
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r)
    (A : Finset (Fin (4 * r))) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => supportWord A ∈ (code sample).carrier) ≤
      (ENNReal.ofReal
        ((1 + Real.exp
          (-2 * ((incidenceProbability (4 * r) Delta).toReal *
            A.card))) / 2)) ^ (3 * r) := by sorry
