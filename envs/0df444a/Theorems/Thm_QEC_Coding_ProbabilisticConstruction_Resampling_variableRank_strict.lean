-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_variableRank_strict
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.variableRank_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:20:21.035029+00:00
-- url     : https://prove2.me/theorems/15beedbd-d74d-484a-8b3a-dccfc5c85233
-- title:
--   Resampling: variable Rank strict
-- statement:
--   The Resampling construction uses the variable Rank strict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/WitnessCompatibility.lean#L34-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/WitnessCompatibility.lean#L34-L48

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessCompatibility
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)

theorem QEC.Coding.ProbabilisticConstruction.Resampling.variableRank_strict (root : I) (P : Finset (List I))
    (p q : List I) (hq : q ∈ P) (v : V) (hqv : v ∈ vars (pathLabel root q))
    (hdepth : p.length < q.length) :
    variableRank vars root P q v < variableRank vars root P p v := by sorry
