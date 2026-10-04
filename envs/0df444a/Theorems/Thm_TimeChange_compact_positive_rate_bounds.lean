-- Prove2me | Theorems.Thm_TimeChange_compact_positive_rate_bounds
-- name    : TimeChange.compact_positive_rate_bounds
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T14:57:48.35484+00:00
-- url     : https://prove2.me/theorems/cc838149-2ff7-498b-933f-c57ee3b4cd49
-- title:
--   Uniform bounds for positive continuous rates on compact sets
-- statement:
--   A positive continuous real-valued rate on a nonempty compact set has a strictly positive uniform lower bound and a finite uniform upper bound. The ambient state space is an arbitrary topological space.
-- source:
--   Original auxiliary extraction from the accepted complete positive-clock/flow proof. Foundations: Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Dynamics/Flow.lean; MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean; MeasureTheory/Integral/DominatedConvergence.lean; Topology/Order/IntermediateValue.lean; Order/Hom/Set.lean. https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib. This is a general topological flow result, without PCR3BP or contact-geometric hypotheses.

import Mathlib.Dynamics.Flow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Hom.Set
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ring
open Set
open scoped Topology ContDiff
set_option maxHeartbeats 800000

theorem TimeChange.compact_positive_rate_bounds {S : Type*} [TopologicalSpace S]
    (K : Set S) (hK : IsCompact K) (hne : K.Nonempty)
    (r : S → ℝ) (hr : ContinuousOn r K) (hpos : ∀ x ∈ K, 0 < r x) :
    ∃ m M : ℝ, 0 < m ∧ ∀ x ∈ K, m ≤ r x ∧ r x ≤ M := by sorry
