-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_prefixCount_stable
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.prefixCount_stable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:28:02.707102+00:00
-- url     : https://prove2.me/theorems/0140e713-9acb-4960-9990-db17e95145f1
-- title:
--   Resampling: prefix Count stable
-- statement:
--   The Resampling construction uses the prefix Count stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Termination.lean#L76-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Termination.lean#L76-L83

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.prefixCount_stable (R : Table (X := X)) (n : ℕ)
    (hn : selected vars bad R n = none) (k : ℕ) (i : I) :
    prefixCount vars bad R (n + k) i = prefixCount vars bad R n i := by sorry
