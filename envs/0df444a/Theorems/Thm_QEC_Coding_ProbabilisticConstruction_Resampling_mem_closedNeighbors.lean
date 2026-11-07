-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.mem_closedNeighbors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:08:56.295526+00:00
-- url     : https://prove2.me/theorems/04a16466-a137-46d8-bbb3-f14c8fe3c079
-- title:
--   Resampling: mem closed Neighbors
-- statement:
--   The Resampling construction uses the mem closed Neighbors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/WitnessTrees.lean#L24-L26
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/WitnessTrees.lean#L24-L26

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open scoped BigOperators
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.mem_closedNeighbors (i j : I) :
    j ∈ closedNeighbors G i ↔ j = i ∨ G.Adj i j := by sorry
