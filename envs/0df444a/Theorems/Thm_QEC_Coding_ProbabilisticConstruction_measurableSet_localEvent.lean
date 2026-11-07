-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_measurableSet_localEvent
-- name    : QEC.Coding.ProbabilisticConstruction.measurableSet_localEvent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:08:57.437205+00:00
-- url     : https://prove2.me/theorems/3033ec37-1bfb-45db-8f20-483fd824dde2
-- title:
--   Probabilistic Construction: measurable Set local Event
-- statement:
--   The Probabilistic Construction construction uses the measurable Set local Event property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/LocalLemma.lean#L207-L210
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/LocalLemma.lean#L207-L210

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]

theorem QEC.Coding.ProbabilisticConstruction.measurableSet_localEvent (vars : I → Finset V)
    (bad : ∀ i, Set (∀ v : vars i, X v)) (hbad : ∀ i, MeasurableSet (bad i))
    (i : I) : MeasurableSet (localEvent vars bad i) := by sorry
