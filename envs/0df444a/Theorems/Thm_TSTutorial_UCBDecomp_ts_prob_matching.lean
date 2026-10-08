-- Prove2me | Theorems.Thm_TSTutorial_UCBDecomp_ts_prob_matching
-- name    : TSTutorial.UCBDecomp.ts_prob_matching
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:51.846478+00:00
-- url     : https://prove2.me/theorems/de85f62d-687c-412a-b3a2-9531e7323270
-- title:
--   §8.1.2, p. 73 — Thompson sampling matches the posterior law of the optimal action
-- statement:
--   Let $x^*(\theta)$ be a measurable optimal action in the Bayesian model, and let $\pi$ be Thompson sampling with the same tie-break. For every history $h$ of $s$ periods and every action $a$,
--
--   $$
--   \Pr_\pi(H_s=h,\ x_{s+1}=a)
--     =\Pr_\pi(H_s=h,\ x^*=a).
--   $$
--
--   This is the probability-matching property used in equation (8.4): conditional on the observed past, the next Thompson-sampling action has the posterior distribution of the optimal action.
--
--   **Formalization Note** The action and outcome sets are finite; the parameter space remains general. The likelihood includes the policy's action probabilities and the outcome kernel. The posterior uses the prior and outcome likelihood, with no restriction on policy behavior at histories of zero evidence.
-- source:
--   Russo, Van Roy, Kazerouni, Osband, Wen, A Tutorial on Thompson Sampling, Found. Trends Mach. Learn. 11(1) (2018), §8.1.2 p. 73, sentence following (8.4)

import Mathlib
import Definitions.Def_TSTutorial_UCBDecomp_Setting

open MeasureTheory
open scoped BigOperators

namespace TSTutorial.UCBDecomp

variable {X Y Θ : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
  [Fintype Y] [DecidableEq Y] [MeasurableSpace Θ]

/-- TS draws the next action from the conditional law of the optimal action (p. 73). -/
theorem ts_prob_matching (m : Model X Y Θ) (xStar : Θ → X)
    (hx : IsOptimalSelector m xStar) (π : Policy X Y)
    (hπ : IsThompsonSampling m xStar π) (s : ℕ)
    (h : Hist X Y s) (a : X) :
    (∑ y : Y, histProb m π (s + 1) (snoc h (a, y))) =
      jointProb m xStar π s a h := by sorry

end TSTutorial.UCBDecomp
