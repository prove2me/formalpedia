-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_supportWord_mem_code_eventMass
-- name    : QEC.Coding.FiberBundle.RandomBase.supportWord_mem_code_eventMass
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:33:38.097762+00:00
-- url     : https://prove2.me/theorems/f5850b41-c75e-4c0c-91a3-7f0e54ad0d36
-- title:
--   Random Base: support Word mem code event Mass
-- statement:
--   Exact probability that the indicator word of a fixed support passes all
--   `3r` parity checks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L322-L363
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L322-L363

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.supportWord_mem_code_eventMass
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (A : Finset (Fin (4 * r))) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => supportWord A ∈ (code sample).carrier) =
      (ENNReal.ofReal
        ((1 +
          (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^
            A.card) / 2)) ^ (3 * r) := by sorry
