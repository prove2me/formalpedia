-- Prove2me | Theorems.Thm_RegretBandits_Nonlinear_sphere_estimate_gradient
-- name    : RegretBandits.Nonlinear.sphere_estimate_gradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:41:20.924464+00:00
-- url     : https://prove2.me/theorems/56a6cfd1-43ce-4402-96de-e89f593d57c7
-- title:
--   Lemma 6.2 — the spherical estimate is an unbiased gradient of the smoothed loss
-- statement:
--   Let $d\ge1$, let $B$ be a random vector uniformly distributed on the closed unit ball $\mathbb B\subset\mathbb R^d$ and $S$ a random vector uniformly distributed on the unit sphere $\mathbb S$. Then for every differentiable $\ell:\mathbb R^d\to\mathbb R$, every $\delta>0$ and every $x\in\mathbb R^d$,
--   $$\frac d\delta\,\mathbb E\big[\ell(x+\delta S)\,S\big]=\nabla\,\mathbb E\,\ell(x+\delta B).$$
--
--   The right-hand side is the gradient of the smoothed loss $\widetilde\ell(x)=\mathbb E\,\ell(x+\delta B)$. The lemma says that the one-point estimate $\frac d\delta\ell(x+\delta S)S$, and by symmetry also the two-point estimate, is an unbiased estimate of $\nabla\widetilde\ell(x)$.
--
--   **Formalization Note** $B$ and $S$ are measurable maps on a probability space whose laws are the uniform distributions on $\mathbb B$ and $\mathbb S$; they need not be independent. The book writes $\ell_t$ in the hypothesis and $\ell$ in the formula; they are the same function.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 91, Lemma 6.2

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_Smoothing

open MeasureTheory

namespace RegretBandits.Nonlinear

/-- Lemma 6.2 (Bubeck, Cesa-Bianchi, arXiv:1204.5721v2, p. 91). Let `d ≥ 1`, let `B` and `S` be
random variables on a probability space `(Ω, P)`, `B` uniform on the closed unit ball `𝔹` of
`ℝ^d` and `S` uniform on the unit sphere `𝕊`. Then for every differentiable `ℓ : ℝ^d → ℝ`, every
`δ > 0` and every `x ∈ ℝ^d`, `(d/δ) E[ℓ(x + δS) S] = ∇ E ℓ(x + δB)`. -/
theorem sphere_estimate_gradient {d : ℕ} (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B S : Ω → EuclideanSpace ℝ (Fin d)) (hBm : Measurable B) (hSm : Measurable S)
    (hB : P.map B = uniformBall d) (hS : P.map S = uniformSphere d)
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ) (hℓ : Differentiable ℝ ℓ)
    (δ : ℝ) (hδ : 0 < δ) (x : EuclideanSpace ℝ (Fin d)) :
    ((d : ℝ) / δ) • ∫ ω, ℓ (x + δ • S ω) • S ω ∂P =
      gradient (fun y => ∫ ω, ℓ (y + δ • B ω) ∂P) x := by sorry

end RegretBandits.Nonlinear
