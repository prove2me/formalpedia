-- Prove2me | Theorems.Thm_RegretBandits_Nonlinear_ball_integral_gradient
-- name    : RegretBandits.Nonlinear.ball_integral_gradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:41:13.679673+00:00
-- url     : https://prove2.me/theorems/42f25168-8ce5-40c5-ad60-1cc485c12657
-- title:
--   Lemma 6.1 — gradient of the ball integral equals the sphere integral (with the factor 1/δ)
-- statement:
--   Let $\mathbb B$ and $\mathbb S$ be the closed unit ball and the unit sphere of $\mathbb R^d$, and let $\sigma$ be the unnormalized spherical (surface) measure on $\mathbb S$. For every differentiable function $\ell:\mathbb R^d\to\mathbb R$, every $\delta>0$ and every $x\in\mathbb R^d$,
--   $$\nabla\int_{\mathbb B}\ell(x+\delta b)\,db=\frac1\delta\int_{\mathbb S}\ell(x+\delta s)\,s\,d\sigma(s),$$
--   where $db$ is Lebesgue measure and the gradient is taken in $x$.
--
--   This is the divergence-theorem identity behind all spherical gradient estimators: the gradient of a ball average of $\ell$ is a sphere average of $\ell$ itself, so it can be estimated from function values only.
--
--   **Formalization Note** Corrected misprint: the book prints the identity without the factor $1/\delta$; the last line of its own proof (p. 91) has it, and Lemma 6.2's $d/\delta$ is consistent only with it. The printed version holds only at $\delta=1$. The verbatim milestone text keeps the printed form.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 90, Lemma 6.1 (proof p. 91)

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_Smoothing

open MeasureTheory

namespace RegretBandits.Nonlinear

/-- Lemma 6.1 (Bubeck, Cesa-Bianchi, arXiv:1204.5721v2, p. 90), in the form its proof (p. 91)
establishes. For every differentiable `ℓ : ℝ^d → ℝ`, every `δ > 0` and every `x ∈ ℝ^d`,
`∇ ∫_𝔹 ℓ(x + δb) db = (1/δ) ∫_𝕊 ℓ(x + δs) s dσ(s)`,
where `db` is Lebesgue measure on the closed unit ball `𝔹` and `σ` is the unnormalized spherical
measure on the unit sphere `𝕊`. Corrected misprint: the printed statement omits the factor `1/δ`,
which the last line of the proof contains. -/
theorem ball_integral_gradient {d : ℕ} (ℓ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hℓ : Differentiable ℝ ℓ) (δ : ℝ) (hδ : 0 < δ) (x : EuclideanSpace ℝ (Fin d)) :
    gradient (fun y => ∫ b in Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
        ℓ (y + δ • b)) x =
      (1 / δ) • ∫ s, ℓ (x + δ • s) • s ∂(sphereMeasure d) := by sorry

end RegretBandits.Nonlinear
