-- Prove2me | Theorems.Thm_PalmQueueing_Ergodic_extremal_flow
-- name    : PalmQueueing.Ergodic.extremal_flow
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T22:13:10.157414+00:00
-- url     : https://prove2.me/theorems/c83efaf7-c2b0-475d-a133-5ac428b4435a
-- title:
--   Theorem 1.6.5 — the extremal characterization of continuous ergodic flows
-- statement:
--   **Theorem 1.6.5 (Extremal property of ergodic flows).** $(P,\{\theta_t\})$ is ergodic if
--   and only if there exists **no** decomposition
--   $$ P = \beta_1 P_1 + \beta_2 P_2, \qquad \beta_1 + \beta_2 = 1, \ \beta_1 > 0, \ \beta_2 > 0,
--   \tag{1.6.6} $$
--   where $P_1$ and $P_2$ are, for all $t \in \mathbb{R}$, $\theta_t$-invariant probabilities on
--   $\Omega$, with $P_1 \ne P_2$.
--
--   The continuous-time counterpart of Theorem 1.6.3, quoted from the same source (Cornfeld, Fomin and
--   Sinai (1981)).
--
--   The difference from the discrete case is in the quantifier and it is not cosmetic: $P_1$ and $P_2$
--   must be invariant under **every** $\theta_t$, not under one map. A probability invariant under a
--   single $\theta_{t_0}$ need not be invariant under the flow.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 50, Theorem 1.6.5

import Mathlib
import Definitions.Def_PalmQueueing_Ergodic_DiscreteFlow

/-!
# Theorem 1.6.5: the extremal characterization of continuous ergodic flows (§1.6.1, p.50)
-/

namespace PalmQueueing.Ergodic

open MeasureTheory
open PalmQueueing.Palm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 1.6.5 (Extremal property of ergodic flows)** (p.50). `(P, {θ_t})` is ergodic if and
only if there exists **no** decomposition

`(1.6.6)  P = β₁P₁ + β₂P₂,  β₁ + β₂ = 1, β₁ > 0, β₂ > 0`,

where `P₁` and `P₂` are, for all `t ∈ ℝ`, `θ_t`-invariant probabilities on `Ω`, with `P₁ ≠ P₂`.

The continuous-time counterpart of Theorem 1.6.3, quoted from the same source (Cornfeld, Fomin and
Sinai (1981)).

The difference from the discrete case is in the quantifier, and it is not cosmetic: `P₁` and `P₂`
must be invariant under **every** `θ_t`, not under one map. A probability invariant under a single
`θ_{t₀}` need not be invariant under the flow. -/
theorem extremal_flow (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Flow Ω) (hinv : θ.Invariant P) :
    IsErgodicFlow θ P ↔ ¬ HasFlowInvariantDecomposition θ P := by sorry

end PalmQueueing.Ergodic
