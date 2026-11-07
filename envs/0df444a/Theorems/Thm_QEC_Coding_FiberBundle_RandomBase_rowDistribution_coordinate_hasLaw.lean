-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_rowDistribution_coordinate_hasLaw
-- name    : QEC.Coding.FiberBundle.RandomBase.rowDistribution_coordinate_hasLaw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:35:36.479264+00:00
-- url     : https://prove2.me/theorems/47f7ca02-0e5b-4e2e-b44d-688448d77def
-- title:
--   Random Base: row Distribution coordinate has Law
-- statement:
--   Every coordinate of a sampled row has the construction's Bernoulli law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L92-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L92-L107

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.rowDistribution_coordinate_hasLaw
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (b : Fin (4 * r)) :
    ProbabilityTheory.HasLaw
      (fun row : RowSample r => row b)
      (PMF.bernoulli
        (incidenceProbability (4 * r) Delta)
        (incidenceProbability_le_one hDelta)).toMeasure
      (rowDistribution r Delta hDelta).toMeasure := by sorry
