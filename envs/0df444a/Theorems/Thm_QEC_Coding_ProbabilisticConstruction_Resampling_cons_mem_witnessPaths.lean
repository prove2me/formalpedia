-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_cons_mem_witnessPaths
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.cons_mem_witnessPaths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:17:16.823311+00:00
-- url     : https://prove2.me/theorems/6eaabc0a-083e-4583-9dfd-e3e7c83a268d
-- title:
--   Resampling: cons mem witness Paths
-- statement:
--   The Resampling construction uses the cons mem witness Paths property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryWitness.lean#L249-L278
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryWitness.lean#L249-L278

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
import Mathlib.Data.Finset.Max
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.cons_mem_witnessPaths (h : ℕ) (root j : I) (t : WitnessTree G (h + 1) root)
    (p : List I) :
    j :: p ∈ witnessPaths G (h + 1) root t ↔
      ∃ hj : j ∈ closedNeighbors G root, ∃ child,
        t ⟨j, hj⟩ = some child ∧ p ∈ witnessPaths G h j child := by sorry
