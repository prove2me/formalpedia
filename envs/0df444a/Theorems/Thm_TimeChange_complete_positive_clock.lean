-- Prove2me | Theorems.Thm_TimeChange_complete_positive_clock
-- name    : TimeChange.complete_positive_clock
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T14:57:51.945087+00:00
-- url     : https://prove2.me/theorems/a04775ae-a4cb-4c33-95f5-ad5987a1facc
-- title:
--   Complete order clock from a continuous rate with a positive lower bound
-- statement:
--   Integrating a continuous real rate bounded below by a positive constant constructs an increasing order equivalence of the whole real line. It starts at zero, has derivative equal to the rate, agrees with the integral from zero, and has a quantitative increment bound. Surjectivity of the clock is proved rather than assumed.
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

theorem TimeChange.complete_positive_clock (r : ℝ → ℝ) (hr : Continuous r)
    (m : ℝ) (hm : 0 < m) (hbound : ∀ t, m ≤ r t) :
    ∃ clock : ℝ ≃o ℝ,
      clock 0 = 0 ∧
      (∀ t, HasDerivAt clock (r t) t) ∧
      (∀ a b : ℝ, a ≤ b → m * (b - a) ≤ clock b - clock a) ∧
      (∀ t, clock t = ∫ s in (0 : ℝ)..t, r s) := by sorry
