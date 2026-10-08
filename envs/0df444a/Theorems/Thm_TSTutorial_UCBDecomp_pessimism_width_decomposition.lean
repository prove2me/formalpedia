-- Prove2me | Theorems.Thm_TSTutorial_UCBDecomp_pessimism_width_decomposition
-- name    : TSTutorial.UCBDecomp.pessimism_width_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:28:56.438811+00:00
-- url     : https://prove2.me/theorems/c68444aa-8315-4f14-904f-77bda41016a0
-- title:
--   §8.1.2, p. 73 — Thompson sampling's per-period regret equals pessimism plus width
-- statement:
--   In the Bayesian decision model, let $x^*(\theta)$ be a measurable optimal action and let $\pi$ follow Thompson sampling with the same selector. For any period $t$ and any history-determined real function $U_t$ on the actions, expected period regret satisfies both equalities
--
--   $$
--   \begin{aligned}
--   \mathbb E_\pi[\mu(x^*,\theta)-\mu(x_t,\theta)]
--     &=\mathbb E_\pi[\mu(x^*,\theta)-U_t(x_t)]
--       +\mathbb E_\pi[U_t(x_t)-\mu(x_t,\theta)]\\
--     &=\underbrace{\mathbb E_\pi[\mu(x^*,\theta)-U_t(x^*)]}_{\text{pessimism}}
--       +\underbrace{\mathbb E_\pi[U_t(x_t)-\mu(x_t,\theta)]}_{\text{width}}.
--   \end{aligned}
--   $$
--
--   The identity is the bridge from upper-confidence-bound analyses to expected-regret bounds for Thompson sampling. The function $U_t$ is an analysis choice; Thompson sampling does not use it to choose actions.
--
--   **Formalization Note** The conclusion records both displayed equalities. Every expectation uses the actual joint law of the same Thompson-sampling policy. The finite action and outcome specialization, measurable kernel and selector, common tie-break, and zero-based Lean periods follow the setting definition.
-- source:
--   Russo, Van Roy, Kazerouni, Osband, Wen, A Tutorial on Thompson Sampling, Found. Trends Mach. Learn. 11(1) (2018), §8.1.2 p. 73, display following (8.4)

import Mathlib
import Definitions.Def_TSTutorial_UCBDecomp_Setting

open MeasureTheory
open scoped BigOperators

namespace TSTutorial.UCBDecomp

variable {X Y Θ : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
  [Fintype Y] [DecidableEq Y] [MeasurableSpace Θ]

/-- The two equalities of the pessimism/width decomposition on p. 73. -/
theorem pessimism_width_decomposition (m : Model X Y Θ) (xStar : Θ → X)
    (hx : IsOptimalSelector m xStar) (π : Policy X Y)
    (hπ : IsThompsonSampling m xStar π) (s : ℕ)
    (U : Hist X Y s → X → ℝ) :
    periodRegret m xStar π s =
      unshiftedPessimism m xStar π s U + width m π s U ∧
    unshiftedPessimism m xStar π s U + width m π s U =
      pessimism m xStar π s U + width m π s U := by sorry

end TSTutorial.UCBDecomp
