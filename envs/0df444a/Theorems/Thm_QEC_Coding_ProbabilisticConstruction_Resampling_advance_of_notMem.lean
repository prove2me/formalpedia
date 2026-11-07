-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_notMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:08:47.021133+00:00
-- url     : https://prove2.me/theorems/5fc1ead7-c364-4ee3-846f-f58ed6e00322
-- title:
--   Resampling: advance of not Mem
-- statement:
--   The Resampling construction uses the advance of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L124-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L124-L126

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
variable {X : V → Type*}

theorem QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_notMem (vars : I → Finset V) (i : I) (c : Counters V)
    {v : V} (hv : v ∉ vars i) : advance vars i c v = c v := by sorry
