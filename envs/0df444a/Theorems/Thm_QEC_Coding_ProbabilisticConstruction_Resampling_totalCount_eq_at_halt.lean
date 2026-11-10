-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_totalCount_eq_at_halt
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.totalCount_eq_at_halt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:27:48.219595+00:00
-- url     : https://prove2.me/theorems/1e3830f7-67c6-42f7-8897-77d41d5984d9
-- title:
--   Resampling: total Count eq at halt
-- statement:
--   The Resampling construction uses the total Count eq at halt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Termination.lean#L85-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Termination.lean#L85-L96

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.totalCount_eq_at_halt (R : Table (X := X)) (n : ℕ)
    (hn : selected vars bad R n = none) (i : I) :
    totalCount vars bad R i = (prefixCount vars bad R n i : ℝ≥0∞) := by sorry
