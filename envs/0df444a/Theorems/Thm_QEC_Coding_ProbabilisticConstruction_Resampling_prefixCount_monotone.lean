-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_prefixCount_monotone
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.prefixCount_monotone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:25:41.154205+00:00
-- url     : https://prove2.me/theorems/b692c3fd-6bce-4e97-81d1-cb1d74a3408d
-- title:
--   Resampling: prefix Count monotone
-- statement:
--   The Resampling construction uses the prefix Count monotone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/OccurrenceCounting.lean#L22-L25
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/OccurrenceCounting.lean#L22-L25

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TreeProbability
import Mathlib.Data.Fintype.Fin
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_OccurrenceCounting
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open scoped BigOperators
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.prefixCount_monotone (R : Table (X := X)) (i : I) :
    Monotone (fun T => prefixCount vars bad R T i) := by sorry
