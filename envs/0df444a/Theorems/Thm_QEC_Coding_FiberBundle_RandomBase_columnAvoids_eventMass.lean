-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnAvoids_eventMass
-- name    : QEC.Coding.FiberBundle.RandomBase.columnAvoids_eventMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:50:37.541424+00:00
-- url     : https://prove2.me/theorems/9653c75b-3a7c-4de4-83cd-fb9a439ccdb4
-- title:
--   Random Base: column Avoids event Mass
-- statement:
--   Exact probability that a sampled column avoids all checks in `S`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L67-L154
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L67-L154

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.columnAvoids_eventMass
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r))) :
    eventMass
        (columnDistribution r Delta hDelta)
        (ColumnAvoids S) =
      (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
        S.card) := by sorry
