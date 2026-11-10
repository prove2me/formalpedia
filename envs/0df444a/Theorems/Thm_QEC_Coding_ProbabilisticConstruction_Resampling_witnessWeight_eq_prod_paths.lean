-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessWeight_eq_prod_paths
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.witnessWeight_eq_prod_paths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:23:11.972046+00:00
-- url     : https://prove2.me/theorems/f9a3664e-032c-4147-acbb-78821d852881
-- title:
--   Resampling: witness Weight eq prod paths
-- statement:
--   Recursive tree weight is the product over its distinct path-addressed nodes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/TreeProbability.lean#L15-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/TreeProbability.lean#L15-L56

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ExecutionWitness
import Mathlib.Data.ENNReal.BigOperators
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TreeProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.witnessWeight_eq_prod_paths (p : I → ℝ) (h : ℕ) (i : I)
    (t : WitnessTree G h i) :
    witnessWeight G p h i t = ∏ q ∈ witnessPaths G h i t, p (pathLabel i q) := by sorry
