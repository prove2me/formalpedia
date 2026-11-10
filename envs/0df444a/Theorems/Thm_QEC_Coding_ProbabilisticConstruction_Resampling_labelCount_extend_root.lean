-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_labelCount_extend_root
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.labelCount_extend_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:17:00.987194+00:00
-- url     : https://prove2.me/theorems/24c72c1c-8a64-40b9-8987-c14c52edd9a9
-- title:
--   Resampling: label Count extend root
-- statement:
--   Every earlier occurrence of the root event is necessarily included.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryWitness.lean#L132-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryWitness.lean#L132-L142

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
import Mathlib.Data.Finset.Max
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.labelCount_extend_root (root j : I) (P : Finset (List I)) (hroot : [] ∈ P) :
    labelCount root root (extendWitness G root j P) =
      labelCount root root P + if j = root then 1 else 0 := by sorry
