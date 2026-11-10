-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_tree_compatibility_probability_le
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.tree_compatibility_probability_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:23:34.244202+00:00
-- url     : https://prove2.me/theorems/46ac146f-a5e2-44dd-a24a-70677bae520c
-- title:
--   Resampling: tree compatibility probability le
-- statement:
--   Every tree's compatibility probability is bounded by its derived product weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/TreeProbability.lean#L76-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/TreeProbability.lean#L76-L87

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ExecutionWitness
import Mathlib.Data.ENNReal.BigOperators
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TreeProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (bad : ∀ i, Set (∀ v : vars i, X v))

theorem QEC.Coding.ProbabilisticConstruction.Resampling.tree_compatibility_probability_le (hbad : ∀ i, MeasurableSet (bad i))
    (h : ℕ) (i : I) (t : WitnessTree (supportGraph vars) h i) :
    tableLaw ν (compatible vars bad i (witnessPaths (supportGraph vars) h i t)) ≤
      ENNReal.ofReal (witnessWeight (supportGraph vars) (eventProbability vars ν bad) h i t) := by sorry
