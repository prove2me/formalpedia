-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_antitone
-- name    : QEC.Coding.ProbabilisticConstruction.avoid_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:18:27.23039+00:00
-- url     : https://prove2.me/theorems/085602fa-02e0-4118-9cff-580df6f7e5a8
-- title:
--   Probabilistic Construction: avoid antitone
-- statement:
--   The Probabilistic Construction construction uses the avoid antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/LocalLemma.lean#L43-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/LocalLemma.lean#L43-L46

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

theorem QEC.Coding.ProbabilisticConstruction.avoid_antitone (B : I → Set Ω) {S T : Finset I} (h : S ⊆ T) :
    avoid B T ⊆ avoid B S := by sorry
