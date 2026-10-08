-- Prove2me | Theorems.Thm_PalmQueueing_Ergodic_extremal_discrete
-- name    : PalmQueueing.Ergodic.extremal_discrete
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T22:04:08.332588+00:00
-- url     : https://prove2.me/theorems/e2f409bf-0c73-44ec-a8fa-3597a8f3f588
-- title:
--   Theorem 1.6.3 — the extremal characterization of discrete ergodic flows
-- statement:
--   **Theorem 1.6.3 (Extremal properties of ergodic flows).** $(P^0_N, \theta)$ is ergodic if
--   and only if there exists **no** decomposition
--   $$ P^0_N = \alpha_1 Q_1 + \alpha_2 Q_2, \qquad \alpha_1 + \alpha_2 = 1, \ \alpha_1 > 0,
--   \ \alpha_2 > 0, \tag{1.6.4} $$
--   where $Q_1$ and $Q_2$ are $\theta$-invariant probabilities with $Q_1 \ne Q_2$.
--
--   Ergodicity is an **extremality** property: the ergodic invariant measures are exactly the extreme
--   points of the convex set of invariant probabilities. That is what makes "ergodic" the right notion
--   of indecomposability and why the ergodic decomposition theorem looks the way it does.
--
--   The book quotes this rather than proving it: "For a proof, see Billingsley (1965), pp. 38-39."
--
--   Stated as an equivalence whose right-hand side is a **negation** — the absence of a decomposition.
--   Stating only that an ergodic flow admits no decomposition would drop the half used in practice.
--
--   **Formalization Note.** A discrete flow is, by the book's definition on p.46, "a bijective and measurable map from $\Omega$ to itself, which preserves $P^0$"; the statement carries `Function.Bijective θ` alongside Mathlib's `Ergodic θ P0` (measure preserving and pre-ergodic).
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 48, Theorem 1.6.3

import Mathlib
import Definitions.Def_PalmQueueing_Ergodic_DiscreteFlow

/-!
# Theorem 1.6.3: the extremal characterization of discrete ergodic flows (§1.6.1, p.48)
-/

namespace PalmQueueing.Ergodic

open MeasureTheory
open PalmQueueing.Palm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 1.6.3 (Extremal properties of ergodic flows)** (p.48). `(P⁰_N, θ)` is ergodic if and
only if there exists **no** decomposition

`(1.6.4)  P⁰_N = α₁Q₁ + α₂Q₂,  α₁ + α₂ = 1, α₁ > 0, α₂ > 0`,

where `Q₁` and `Q₂` are `θ`-invariant probabilities with `Q₁ ≠ Q₂`.

Ergodicity is an **extremality** property: the ergodic invariant measures are exactly the extreme
points of the convex set of invariant probabilities. That is what makes "ergodic" the right notion
of indecomposability, and it is why the ergodic decomposition theorem looks the way it does.

The book quotes this result rather than proving it: "For a proof, see Billingsley (1965),
pp. 38-39."

The statement is an equivalence, and its right-hand side is a **negation** — the absence of a
decomposition. Stating only that an ergodic flow admits no decomposition would drop the half that
is used in practice.

`hbij` is the book's definition of a discrete flow (p.46). -/
theorem extremal_discrete (P0 : Measure Ω) [IsProbabilityMeasure P0]
    (θ : Ω → Ω) (hθ : Measurable θ) (hbij : Function.Bijective θ) (hinv : Measure.map θ P0 = P0) :
    Ergodic θ P0 ↔ ¬ HasInvariantDecomposition θ P0 := by sorry

end PalmQueueing.Ergodic
