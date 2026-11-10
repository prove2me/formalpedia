-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPaths_pathsToTree
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.witnessPaths_pathsToTree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:16:59.601121+00:00
-- url     : https://prove2.me/theorems/b59be010-fb1f-4c46-a3ed-643bc561e05c
-- title:
--   Resampling: witness Paths paths To Tree
-- statement:
--   Encoding retains every node and introduces none; hence it is injective on proper paths.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryWitness.lean#L281-L319
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryWitness.lean#L281-L319

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
import Mathlib.Data.Finset.Max
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.witnessPaths_pathsToTree (h : ℕ) (root : I) (P : Finset (List I))
    (hP : ProperPaths G root P) (hd : ∀ p ∈ P, p.length < h) :
    witnessPaths G h root (pathsToTree G h root P hP hd) = P := by sorry
