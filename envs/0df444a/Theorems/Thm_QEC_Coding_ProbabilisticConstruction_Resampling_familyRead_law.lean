-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_familyRead_law
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.familyRead_law
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:19:45.055735+00:00
-- url     : https://prove2.me/theorems/c24c1005-4c16-4aef-b652-c76b99c45f5a
-- title:
--   Resampling: family Read law
-- statement:
--   Distinct addresses transfer the independent table law to a finite product of local laws.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/TableProbability.lean#L32-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/TableProbability.lean#L32-L50

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.familyRead_law (coords : A → Finset V) (column : ∀ a, coords a → ℕ)
    (haddress : Function.Injective
      (fun s : (a : A) × coords a => (s.2.val, column s.1 s.2))) :
    (tableLaw ν).map (familyRead (X := X) coords column) =
      Measure.pi (fun a => Measure.pi (fun v : coords a => ν v)) := by sorry
