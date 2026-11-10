-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_prefixCount_strict
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.prefixCount_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:26:01.286881+00:00
-- url     : https://prove2.me/theorems/9bf3bf98-c7ad-4d7e-9789-05fa7cd622ae
-- title:
--   Resampling: prefix Count strict
-- statement:
--   The Resampling construction uses the prefix Count strict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/OccurrenceCounting.lean#L27-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/OccurrenceCounting.lean#L27-L36

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.prefixCount_strict (R : Table (X := X)) (i : I) (a b : ℕ)
    (hab : a < b) (ha : selected vars bad R a = some i) :
    prefixCount vars bad R a i < prefixCount vars bad R b i := by sorry
