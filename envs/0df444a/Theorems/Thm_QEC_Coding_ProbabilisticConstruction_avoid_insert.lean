-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
-- name    : QEC.Coding.ProbabilisticConstruction.avoid_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:08:19.348088+00:00
-- url     : https://prove2.me/theorems/9b178dcd-9027-4455-b8a8-5c7f24801aa3
-- title:
--   Probabilistic Construction: avoid insert
-- statement:
--   The Probabilistic Construction construction uses the avoid insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/LocalLemma.lean#L31-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/LocalLemma.lean#L31-L36

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]

theorem QEC.Coding.ProbabilisticConstruction.avoid_insert (B : I → Set Ω) (i : I) (S : Finset I) :
    avoid B (insert i S) = avoid B S \ B i := by sorry
