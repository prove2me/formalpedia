-- Prove2me | Theorems.Thm_RegretBandits_Nonlinear_osgd_one_point_regret_bound
-- name    : RegretBandits.Nonlinear.osgd_one_point_regret_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:43:10.676013+00:00
-- url     : https://prove2.me/theorems/96ed7b20-57a1-4553-8efb-55548c40d9e1
-- title:
--   Theorem 6.2 (first display) — pseudo-regret of OSGD with one-point feedback
-- statement:
--   Let $d\ge1$ and let $\mathcal K\subseteq\mathbb R^d$ be closed and convex with $r\,\mathbb B\subseteq\mathcal K\subseteq R\,\mathbb B$ for some $r,R>0$. Let $\ell_1,\ell_2,\dots:\mathbb R^d\to\mathbb R$ be a fixed sequence of $G$-Lipschitz, differentiable and convex losses with $|\ell_t(y)|\le L$ for all $y\in\mathcal K$. Fix $\delta$ with $0<\delta\le r$ and a learning rate $\eta>0$.
--
--   On a probability space let $S_1,S_2,\dots$ be independent and uniform on the unit sphere $\mathbb S$. Run OSGD on $(1-\delta/r)\mathcal K$ with learning rate $\eta$ and the one-point estimates (6.3)
--   $$\widetilde g_t(x_t)=\frac d\delta\,\ell_t(\widetilde X_t)\,S_t,\qquad \widetilde X_t=x_t+\delta S_t,$$
--   playing $\widetilde X_t$ at round $t$. Then
--   $$\overline R_n=\mathbb E\sum_{t=1}^n\ell_t(\widetilde X_t)-\min_{x\in\mathcal K}\sum_{t=1}^n\ell_t(x)\le\frac{R^2}{\eta}+\frac{(dL)^2}{\delta^2}\,\eta n+\delta\Big(3+\frac Rr\Big)Gn .$$
--
--   Only the value of the loss at the single played point is observed in each round.
--
--   **Formalization Note** Added hypothesis $\delta\le r$, not printed but needed by the proof so that $\widetilde X_t\in\mathcal K$. A convex function bounded on all of $\mathbb R^d$ is constant, so the book's $\|\ell\|_\infty\le L$ is read as the bound on $\mathcal K$, as the text on p. 95 says ("the maximum value of each $\ell_t$ in $\mathcal K$ is bounded by $L$"). The losses are oblivious and are Lipschitz, differentiable and convex on all of $\mathbb R^d$. The constant $R^2/\eta$ is the book's form.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 95, Theorem 6.2 (first display)

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_Smoothing
import Definitions.Def_RegretBandits_Nonlinear_OSGD

open MeasureTheory ProbabilityTheory
open scoped NNReal Pointwise

namespace RegretBandits.Nonlinear

/-- Theorem 6.2, first display (Bubeck, Cesa-Bianchi, arXiv:1204.5721v2, p. 95): regret of OSGD
with one-point feedback. Let `d ≥ 1` and let `K ⊆ ℝ^d` be closed and convex with
`r𝔹 ⊆ K ⊆ R𝔹`, `r, R > 0`. Let `ℓ_1, ℓ_2, … : ℝ^d → ℝ` be a fixed sequence of `G`-Lipschitz,
differentiable and convex losses with `|ℓ_t| ≤ L` on `K`. Fix `0 < δ ≤ r` (the bound `δ ≤ r`
is not printed; the proof needs it) and `η > 0`. On a probability space, let `S_1, S_2, …` be
independent and uniform on the unit sphere, let `x_t` be the OSGD run on `(1 - δ/r)K` with
learning rate `η` and the one-point estimates (6.3) `g̃_t(x_t) = (d/δ) ℓ_t(X̃_t) S_t`, where
`X̃_t = x_t + δS_t` is the played point. Then `R̄_n ≤ R²/η + ((dL)²/δ²) ηn + δ(3 + R/r)Gn`. -/
theorem osgd_one_point_regret_bound
    {d : ℕ} (hd : 1 ≤ d)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hKclosed : IsClosed K) (hKconv : Convex ℝ K)
    (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (hrK : Metric.closedBall 0 r ⊆ K) (hKR : K ⊆ Metric.closedBall 0 R)
    (G : ℝ≥0) (ℓ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hℓlip : ∀ t, LipschitzWith G (ℓ t)) (hℓdiff : ∀ t, Differentiable ℝ (ℓ t))
    (hℓconv : ∀ t, ConvexOn ℝ Set.univ (ℓ t))
    (L : ℝ) (hℓbdd : ∀ t, ∀ y ∈ K, |ℓ t y| ≤ L)
    (δ η : ℝ) (hδ : 0 < δ) (hδr : δ ≤ r) (hη : 0 < η)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hSm : ∀ t, Measurable (S t))
    (hind : iIndepFun S P) (hlaw : ∀ t, P.map (S t) = uniformSphere d)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hx : ∀ ω, IsOSGDRun ((1 - δ / r) • K) η
      (fun t y => onePointEstimate d δ (ℓ t) (S t ω) y) (fun t => x t ω))
    (n : ℕ) :
    pseudoRegret K ℓ P (fun t ω => x t ω + δ • S t ω) n ≤
      R ^ 2 / η + ((d : ℝ) * L) ^ 2 / δ ^ 2 * η * n + δ * (3 + R / r) * G * n := by sorry

end RegretBandits.Nonlinear
