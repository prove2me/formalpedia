-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_rowDistribution_iIndepFun
-- name    : QEC.Coding.FiberBundle.RandomBase.rowDistribution_iIndepFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:34:53.173204+00:00
-- url     : https://prove2.me/theorems/fc8ac914-2c1c-40a5-889e-d79c478a1f2e
-- title:
--   Random Base: row Distribution i Indep Fun
-- statement:
--   Incidences within one sampled row are mutually independent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L84-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L84-L89

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.rowDistribution_iIndepFun
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.iIndepFun
      (fun b (row : RowSample r) => row b)
      (rowDistribution r Delta hDelta).toMeasure := by sorry
