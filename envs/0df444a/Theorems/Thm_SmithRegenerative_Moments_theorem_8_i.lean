-- Prove2me | Theorems.Thm_SmithRegenerative_Moments_theorem_8_i
-- name    : SmithRegenerative.Moments.theorem_8_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:35:23.677787+00:00
-- url     : https://prove2.me/theorems/4432fd77-40d3-40df-8a60-9975e5ae88c3
-- title:
--   Theorem 8(i) — mean growth of a cumulative process
-- statement:
--   Let $w_t$ be a cumulative process with first cycle mean length $\mu_1$ and mean reward $\kappa_1$. If $t_1$ and the first cycle's total variation $\tilde y_1$ are integrable, then $w_t$ is integrable at every $t\geq0$ and
--
--   $$
--   \mathbb E w_t=\frac{\kappa_1}{\mu_1}t+o(t)\qquad(t\to\infty).
--   $$
--
--   This is the first part of Smith's mean-and-variance theorem and a milestone for its joint formalization.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 28, Theorem 8(i), (5·3·6)

import Mathlib
import Definitions.Def_SmithRegenerative_Moments_CumulativeProcess

namespace SmithRegenerative.Moments

open MeasureTheory Filter

/-- Smith, *Regenerative stochastic processes*, Proc. R. Soc. Lond. A
232(1188):6–31 (1955), p. 28, Theorem 8(i), (5·3·6).
Formalization Note: `κ̃₁ < ∞` is expressed by integrability of the first
cycle's variation. The mean is a genuine integral on every nonnegative time. -/
theorem theorem_8_i {Ω : Type*} [MeasurableSpace Ω]
    (C : CumulativeProcess Ω)
    (hμ : Integrable (C.renewal.cycleLength 1) C.renewal.P)
    (hvar : Integrable (cycleVariation C.renewal C.w 1) C.renewal.P) :
    (∀ t : ℝ, 0 ≤ t → Integrable (C.w t) C.renewal.P) ∧
    (fun t : ℝ =>
      (∫ ω, C.w t ω ∂C.renewal.P) -
        C.meanReward / C.meanLength * t) =o[atTop] (fun t : ℝ => t) := by sorry

end SmithRegenerative.Moments
