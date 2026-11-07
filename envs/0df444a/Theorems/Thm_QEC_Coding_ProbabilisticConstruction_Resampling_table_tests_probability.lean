-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_table_tests_probability
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.table_tests_probability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:42:22.805809+00:00
-- url     : https://prove2.me/theorems/9b869a4f-e186-4633-8cc2-212a2a1a0234
-- title:
--   Resampling: table tests probability
-- statement:
--   The finite compatibility probability is derived from the table law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/TableProbability.lean#L53-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/TableProbability.lean#L53-L63

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.table_tests_probability (coords : A → Finset V) (column : ∀ a, coords a → ℕ)
    (haddress : Function.Injective
      (fun s : (a : A) × coords a => (s.2.val, column s.1 s.2)))
    (test : ∀ a, Set (∀ v : coords a, X v)) (htest : ∀ a, MeasurableSet (test a)) :
    tableLaw ν {R | ∀ a, familyRead coords column R a ∈ test a} =
      ∏ a, (Measure.pi (fun v : coords a => ν v)) (test a) := by sorry
