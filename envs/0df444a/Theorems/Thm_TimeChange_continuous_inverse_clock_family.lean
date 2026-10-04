-- Prove2me | Theorems.Thm_TimeChange_continuous_inverse_clock_family
-- name    : TimeChange.continuous_inverse_clock_family
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T14:57:56.770358+00:00
-- url     : https://prove2.me/theorems/ea58d9a5-6759-41ea-8071-c86c0c0283ea
-- title:
--   Joint continuity of inverse families of real order equivalences
-- statement:
--   A family of real order equivalences indexed by an arbitrary topological space has a jointly continuous inverse evaluation map whenever its forward evaluation map is jointly continuous. No differentiability or compactness assumption is needed.
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

theorem TimeChange.continuous_inverse_clock_family {S : Type*} [TopologicalSpace S]
    (c : S → (ℝ ≃o ℝ)) (hc : Continuous (fun p : ℝ × S => c p.2 p.1)) :
    Continuous (fun p : ℝ × S => (c p.2).symm p.1) := by sorry
