-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_halt_absorbing
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.halt_absorbing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:42:04.70321+00:00
-- url     : https://prove2.me/theorems/99852601-1261-413f-9853-7db9c7a0017f
-- title:
--   Resampling: halt absorbing
-- statement:
--   The Resampling construction uses the halt absorbing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L205-L214
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L205-L214

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
variable {X : V → Type*}
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.halt_absorbing (R : Table (X := X)) (n : ℕ)
    (h : selected vars bad R n = none) (k : ℕ) :
    counters vars bad R (n + k) = counters vars bad R n ∧
      selected vars bad R (n + k) = none := by sorry
