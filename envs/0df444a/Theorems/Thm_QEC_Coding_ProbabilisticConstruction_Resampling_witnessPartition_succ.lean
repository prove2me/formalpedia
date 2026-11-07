-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_succ
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:21:38.302969+00:00
-- url     : https://prove2.me/theorems/4237ddfb-4d02-4357-8cfe-2c6aa078d67b
-- title:
--   Resampling: witness Partition succ
-- statement:
--   The Resampling construction uses the witness Partition succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/WitnessTrees.lean#L58-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/WitnessTrees.lean#L58-L71

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open scoped BigOperators
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_succ (p : I → ℝ) (h : ℕ) (i : I) :
    witnessPartition G p (h + 1) i =
      p i * ∏ j ∈ closedNeighbors G i, (1 + witnessPartition G p h j) := by sorry
