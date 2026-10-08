-- Prove2me | Theorems.Thm_RegretBandits_Nonlinear_smoothed_regret_comparison
-- name    : RegretBandits.Nonlinear.smoothed_regret_comparison
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T10:42:07.530776+00:00
-- url     : https://prove2.me/theorems/8a20223e-6da1-4985-a82f-f63533a36a82
-- title:
--   Lemma 6.3 — regret under the losses vs. regret under the smoothed losses
-- statement:
--   Let $d\ge1$, let $\mathcal K\subseteq\mathbb R^d$ be convex with $\mathcal K\subseteq R\,\mathbb B$ for some $R\ge0$, and fix $0\le\xi\le1$ and $\delta>0$. Let $\ell_1,\ell_2,\dots:\mathbb R^d\to\mathbb R$ be $G$-Lipschitz, differentiable and convex, with smoothed versions $\widetilde\ell_t(y)=\mathbb E\,\ell_t(y+\delta B)$. Let $x_1,x_2,\dots\in(1-\xi)\mathcal K$, let $S_1,S_2,\dots$ be arbitrary points of the unit sphere, and put $X_t^+=x_t+\delta S_t$, $X_t^-=x_t-\delta S_t$. Then for every $n$ and every $x\in\mathcal K$,
--   $$\frac12\sum_{t=1}^n\big(\ell_t(X_t^+)+\ell_t(X_t^-)\big)-\sum_{t=1}^n\ell_t(x)\le\sum_{t=1}^n\widetilde\ell_t(x_t)-\sum_{t=1}^n\widetilde\ell_t\big((1-\xi)x\big)+3\delta Gn+\xi GRn .$$
--
--   The lemma reduces the regret of the queried points against $x$ to the regret of the OSGD iterates against the shrunken comparator $(1-\xi)x$ under the smoothed losses.
--
--   **Formalization Note** "For all realizations of the random process $(X_t^+,X_t^-)_{t\ge1}$" is encoded by quantifying over every sequence $S_t$ of unit vectors; the statement is deterministic. The comparator $x$, implicit in the book, ranges over $\mathcal K$ (the proof uses $\|x\|\le R$). The losses are Lipschitz on all of $\mathbb R^d$.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 92, Lemma 6.3 (X+_t, X-_t defined on p. 90)

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_Smoothing

open MeasureTheory
open scoped NNReal Pointwise

namespace RegretBandits.Nonlinear

/-- Lemma 6.3 (Bubeck, Cesa-Bianchi, arXiv:1204.5721v2, p. 92). Let `d ≥ 1`, let `K ⊆ ℝ^d` be
convex with `K ⊆ R𝔹` for some `R ≥ 0`, and fix `0 ≤ ξ ≤ 1` and `δ > 0`. Let `ℓ_1, ℓ_2, …` be
`G`-Lipschitz, differentiable and convex losses `ℝ^d → ℝ`, let `x_1, x_2, … ∈ (1 - ξ)K`, and let
`S_1, S_2, …` be any points of the unit sphere (a realization of the random directions), with
`X⁺_t = x_t + δS_t`, `X⁻_t = x_t - δS_t`. Then for every `n` and every `x ∈ K`,
`(1/2) ∑_{t=1}^n (ℓ_t(X⁺_t) + ℓ_t(X⁻_t)) - ∑_{t=1}^n ℓ_t(x)
  ≤ ∑_{t=1}^n ℓ̃_t(x_t) - ∑_{t=1}^n ℓ̃_t((1 - ξ)x) + 3δGn + ξGRn`,
where `ℓ̃_t(y) = E ℓ_t(y + δB)` is the smoothed loss. -/
theorem smoothed_regret_comparison {d : ℕ} (hd : 1 ≤ d)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hKconv : Convex ℝ K)
    (R : ℝ) (hR : 0 ≤ R) (hKR : K ⊆ Metric.closedBall 0 R)
    (ξ : ℝ) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (δ : ℝ) (hδ : 0 < δ) (G : ℝ≥0)
    (ℓ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (hℓlip : ∀ t, LipschitzWith G (ℓ t))
    (hℓdiff : ∀ t, Differentiable ℝ (ℓ t)) (hℓconv : ∀ t, ConvexOn ℝ Set.univ (ℓ t))
    (xs : ℕ → EuclideanSpace ℝ (Fin d)) (hxs : ∀ t, xs t ∈ (1 - ξ) • K)
    (S : ℕ → EuclideanSpace ℝ (Fin d)) (hS : ∀ t, ‖S t‖ = 1)
    (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ K) :
    (1 / 2) * ∑ t ∈ Finset.Icc 1 n, (ℓ t (xs t + δ • S t) + ℓ t (xs t - δ • S t))
        - ∑ t ∈ Finset.Icc 1 n, ℓ t x ≤
      ∑ t ∈ Finset.Icc 1 n, smoothedLoss d δ (ℓ t) (xs t)
        - ∑ t ∈ Finset.Icc 1 n, smoothedLoss d δ (ℓ t) ((1 - ξ) • x)
        + 3 * δ * G * n + ξ * G * R * n := by sorry

end RegretBandits.Nonlinear
