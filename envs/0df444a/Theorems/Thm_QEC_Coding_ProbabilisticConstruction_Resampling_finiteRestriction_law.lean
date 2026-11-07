-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_finiteRestriction_law
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.finiteRestriction_law
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:19:47.026937+00:00
-- url     : https://prove2.me/theorems/3dd4bf37-9d5f-4500-a386-0e7412579c64
-- title:
--   Resampling: finite Restriction law
-- statement:
--   Restricting the full finite variable law gives its actual coordinate product law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/TableProbability.lean#L66-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/TableProbability.lean#L66-L72

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.finiteRestriction_law (S : Finset V) :
    (Measure.pi ν).map S.restrict = Measure.pi (fun v : S => ν v) := by sorry
