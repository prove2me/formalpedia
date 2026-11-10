-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_prefixCount_le_compatible
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.prefixCount_le_compatible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:26:00.929923+00:00
-- url     : https://prove2.me/theorems/0fc6f5bc-1cd2-4060-92c5-a9971f1a3f2a
-- title:
--   Resampling: prefix Count le compatible
-- statement:
--   A finite execution count is bounded pointwise by the compatible-tree count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/OccurrenceCounting.lean#L119-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/OccurrenceCounting.lean#L119-L128

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
open scoped Classical

theorem QEC.Coding.ProbabilisticConstruction.Resampling.prefixCount_le_compatible (R : Table (X := X)) (T : ℕ) (i : I) :
    prefixCount vars bad R T i ≤
      (Finset.univ.filter (fun t : WitnessTree (supportGraph vars) (T + 1) i =>
        R ∈ compatible vars bad i (witnessPaths (supportGraph vars) (T + 1) i t))).card := by sorry
