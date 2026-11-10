-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_prefixCount_succ
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.prefixCount_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:27:16.70553+00:00
-- url     : https://prove2.me/theorems/1563aece-5ab8-4fa2-ac3a-fbb9dd0fc659
-- title:
--   Resampling: prefix Count succ
-- statement:
--   The Resampling construction uses the prefix Count succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Termination.lean#L15-L20
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Termination.lean#L15-L20

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.prefixCount_succ (R : Table (X := X)) (T : ℕ) (i : I) :
    prefixCount vars bad R (T + 1) i = prefixCount vars bad R T i +
      if selected vars bad R T = some i then 1 else 0 := by sorry
