-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_HasDependencyGraph_factor_avoid
-- name    : QEC.Coding.ProbabilisticConstruction.HasDependencyGraph.factor_avoid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:18:32.048191+00:00
-- url     : https://prove2.me/theorems/707368d6-7e3f-4efa-9ea3-340afbbff1fd
-- title:
--   Has Dependency Graph: factor avoid
-- statement:
--   The Has Dependency Graph construction uses the factor avoid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/LocalLemma.lean#L60-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/LocalLemma.lean#L60-L79

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

theorem QEC.Coding.ProbabilisticConstruction.HasDependencyGraph.factor_avoid {μ : Measure Ω} {B : I → Set Ω}
    {G : SimpleGraph I} (h : HasDependencyGraph μ B G) (i : I) (S : Finset I)
    (hS : ∀ j ∈ S, j ≠ i ∧ ¬ G.Adj i j) :
    μ.real (B i ∩ avoid B S) = μ.real (B i) * μ.real (avoid B S) := by sorry
