-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_variableRank_injective
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.variableRank_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:20:24.287811+00:00
-- url     : https://prove2.me/theorems/ec332827-f690-4dac-a6d9-e1e348945fb9
-- title:
--   Resampling: variable Rank injective
-- statement:
--   The Resampling construction uses the variable Rank injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/WitnessCompatibility.lean#L50-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/WitnessCompatibility.lean#L50-L63

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessCompatibility
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)

theorem QEC.Coding.ProbabilisticConstruction.Resampling.variableRank_injective (root : I) (P : Finset (List I))
    (hd : DistinctVariableDepth vars root P) (p q : List I) (hp : p ∈ P) (hq : q ∈ P)
    (v : V) (hpv : v ∈ vars (pathLabel root p)) (hqv : v ∈ vars (pathLabel root q))
    (he : variableRank vars root P p v = variableRank vars root P q v) : p = q := by sorry
