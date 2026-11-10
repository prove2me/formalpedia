-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_candidate_of_shared_variable
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.candidate_of_shared_variable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:17:35.64754+00:00
-- url     : https://prove2.me/theorems/37fb67cb-b11f-4d39-b414-23a7c6ebc1f0
-- title:
--   Resampling: candidate of shared variable
-- statement:
--   The Resampling construction uses the candidate of shared variable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryTimes.lean#L134-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryTimes.lean#L134-L143

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)

theorem QEC.Coding.ProbabilisticConstruction.Resampling.candidate_of_shared_variable (root j : I) (P : Finset (List I))
    (p : List I) (hp : p ∈ P) (v : V) (hj : v ∈ vars j)
    (hv : v ∈ vars (pathLabel root p)) :
    p ∈ attachmentCandidates (supportGraph vars) root j P := by sorry
