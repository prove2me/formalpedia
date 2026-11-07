-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_rowParityZero_eventMass
-- name    : QEC.Coding.FiberBundle.RandomBase.rowParityZero_eventMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:39:24.287392+00:00
-- url     : https://prove2.me/theorems/d1582fb3-3c4d-4b02-9906-75a2b808ec46
-- title:
--   Random Base: row Parity Zero event Mass
-- statement:
--   ENNReal form of the exact one-row parity probability.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L227-L246
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L227-L246

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.rowParityZero_eventMass
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (A : Finset (Fin (4 * r))) :
    eventMass
        (rowDistribution r Delta hDelta)
        (RowParityZero A) =
      ENNReal.ofReal
        ((1 +
          (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^ A.card) / 2) := by sorry
