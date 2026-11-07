-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnHits_eventMass
-- name    : QEC.Coding.FiberBundle.RandomBase.columnHits_eventMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:51:33.959368+00:00
-- url     : https://prove2.me/theorems/8d3b669f-733c-4974-9488-9debdb5b0682
-- title:
--   Random Base: column Hits event Mass
-- statement:
--   Exact probability that a sampled column is hit by `S`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L157-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L157-L201

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.columnHits_eventMass
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r))) :
    eventMass
        (columnDistribution r Delta hDelta)
        (ColumnHits S) =
      1 -
        (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
          S.card) := by sorry
