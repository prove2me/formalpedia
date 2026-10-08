-- Prove2me | Theorems.Thm_RiskSensMDP_Discounted_operator_preserves_class
-- name    : RiskSensMDP.Discounted.operator_preserves_class
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:28:43.898986+00:00
-- url     : https://prove2.me/theorems/c7ab99da-f3c6-455e-83ff-44afcc2be374
-- title:
--   Proof of Theorem 3.6 — the operator preserves C(Ê) and admits a minimizer
-- statement:
--   In the discounted model under (CC), let $v\in C(\hat E)$ and suppose its one-step continuation is integrable under $Q(\cdot\mid x,a)$ for every admissible $(x,y,z,a)$. Then the minimum operator preserves the value-function class and has a measurable admissible minimizing rule:
--
--   $$Tv\in C(\hat E),\qquad \exists f\in F\;\;T_fv=Tv\text{ on }\hat E.$$
--
--   This is the regularity and selection step used by finite-horizon value iteration. **Formalization Note** The source states the result for every real-valued $v\in C(\hat E)$, without integrability. On an unbounded state space this does not ensure a finite expectation, while Lean's real integral returns zero for a nonintegrable function. The explicit integrability condition records the needed domain correction.
-- source:
--   Bäuerle & Rieder, More Risk-Sensitive Markov Decision Processes, authors' manuscript (KIT repository 1000039663; published Math. Oper. Res. 39(1):105–120, 2014), p. 12, §3.3, proof of Theorem 3.6

import Mathlib
import Definitions.Def_RiskSensMDP_Discounted_Model

open MeasureTheory ProbabilityTheory Filter

namespace RiskSensMDP.Discounted

/-- §3.3, proof of Theorem 3.6, authors' manuscript p. 12: `T` maps
`C(Ê)` into itself and admits a measurable, admissible minimizer.
Formalization Note: one-step integrability is made explicit because the paper's
real-valued `C(Ê)` permits functions whose expectation is infinite. -/
theorem operator_preserves_class {E A : Type*}
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.MetrizableSpace E] [SecondCountableTopology E]
    [StandardBorelSpace E]
    [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [StandardBorelSpace A]
    (M : Model E A) (hBounds : HasBounds M) (hCC : HasCC M)
    (v : ExtendedState E → ℝ) (hv : InClass M v)
    (hInt : ContinuationIntegrable M v) :
    InClass M (minimumOperator M v) ∧
      ∃ f : DecisionRule M, IsMinimizer M v f := by sorry

end RiskSensMDP.Discounted
