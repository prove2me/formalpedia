-- Prove2me | Theorems.Thm_RegretBandits_Nonlinear_osgd_one_point_regret_tuned
-- name    : RegretBandits.Nonlinear.osgd_one_point_regret_tuned
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:43:09.873187+00:00
-- url     : https://prove2.me/theorems/ea91d3bd-8671-4def-8b0e-b538e9b7b9d9
-- title:
--   Theorem 6.2 — OSGD with one-point feedback has pseudo-regret at most 4n^{3/4}√(RdL(3+R/r)G)
-- statement:
--   Let $d\ge1$ and let $\mathcal K\subseteq\mathbb R^d$ be closed and convex with $r\,\mathbb B\subseteq\mathcal K\subseteq R\,\mathbb B$ for some $r,R>0$. Let $\ell_1,\ell_2,\dots:\mathbb R^d\to\mathbb R$ be a fixed sequence of $G$-Lipschitz, differentiable and convex losses with $|\ell_t|\le L$ on $\mathcal K$, where $G,L>0$. Let $n\ge1$ and
--   $$\delta=\frac{1}{(2n)^{1/4}}\sqrt{\frac{RdL}{(3+\frac Rr)G}},\qquad \eta=\frac{1}{(2n)^{3/4}}\sqrt{\frac{R^3}{dL(3+\frac Rr)G}},$$
--   and assume $\delta\le r$. Let $S_1,S_2,\dots$ be independent and uniform on the unit sphere, and run OSGD on $(1-\delta/r)\mathcal K$ with learning rate $\eta$ and the one-point estimates $\widetilde g_t(x_t)=\frac d\delta\ell_t(\widetilde X_t)S_t$, playing $\widetilde X_t=x_t+\delta S_t$. Then
--   $$\overline R_n=\mathbb E\sum_{t=1}^n\ell_t(\widetilde X_t)-\min_{x\in\mathcal K}\sum_{t=1}^n\ell_t(x)\le 4n^{3/4}\sqrt{RdL\Big(3+\frac Rr\Big)G}.$$
--
--   This is the $\mathcal O(n^{3/4})$ pseudo-regret of bandit convex optimization with one-point feedback.
--
--   **Formalization Note** Added hypothesis $\delta\le r$ (not printed; the proof needs $\widetilde X_t\in\mathcal K$). For this $\delta$ it is a condition on $n$, holding for all $n$ large enough. $G>0$, $L>0$, $n\ge1$ are needed for $\delta,\eta$ to be defined and positive. The constant $4$ is the book's rounding of the $2\cdot2^{3/4}\approx3.36$ the stated $\delta,\eta$ give; it is kept. The bound on the losses is on $\mathcal K$ (see Theorem 6.2, first display).
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 95, Theorem 6.2 (second display)

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_Smoothing
import Definitions.Def_RegretBandits_Nonlinear_OSGD

open MeasureTheory ProbabilityTheory
open scoped NNReal Pointwise

namespace RegretBandits.Nonlinear

/-- Theorem 6.2, second display (Bubeck, Cesa-Bianchi, arXiv:1204.5721v2, p. 95). In the setting
of Theorem 6.2 (`d ≥ 1`, `K` closed convex with `r𝔹 ⊆ K ⊆ R𝔹`, `G`-Lipschitz differentiable
convex losses with `|ℓ_t| ≤ L` on `K`, OSGD on `(1 - δ/r)K` with the one-point estimates (6.3),
independent uniform directions `S_t`, played point `X̃_t = x_t + δS_t`), assume `G > 0`,
`L > 0`, `n ≥ 1` and
`δ = (2n)^{-1/4} √(RdL / ((3 + R/r)G))`, `η = (2n)^{-3/4} √(R³ / (dL(3 + R/r)G))`,
and assume this `δ` satisfies `δ ≤ r` (not printed; the proof needs it, and for this `δ` it is a
condition on `n`). Then `R̄_n ≤ 4 n^{3/4} √(RdL(3 + R/r)G)`. -/
theorem osgd_one_point_regret_tuned
    {d : ℕ} (hd : 1 ≤ d)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hKclosed : IsClosed K) (hKconv : Convex ℝ K)
    (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (hrK : Metric.closedBall 0 r ⊆ K) (hKR : K ⊆ Metric.closedBall 0 R)
    (G : ℝ≥0) (ℓ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hℓlip : ∀ t, LipschitzWith G (ℓ t)) (hℓdiff : ∀ t, Differentiable ℝ (ℓ t))
    (hℓconv : ∀ t, ConvexOn ℝ Set.univ (ℓ t))
    (L : ℝ) (hℓbdd : ∀ t, ∀ y ∈ K, |ℓ t y| ≤ L)
    (hG : 0 < G) (hL : 0 < L) (δ η : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hSm : ∀ t, Measurable (S t))
    (hind : iIndepFun S P) (hlaw : ∀ t, P.map (S t) = uniformSphere d)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hx : ∀ ω, IsOSGDRun ((1 - δ / r) • K) η
      (fun t y => onePointEstimate d δ (ℓ t) (S t ω) y) (fun t => x t ω))
    (n : ℕ)
    (hn : 0 < n)
    (hδdef : δ = 1 / (2 * (n : ℝ)) ^ ((1 : ℝ) / 4) *
      Real.sqrt (R * d * L / ((3 + R / r) * G)))
    (hηdef : η = 1 / (2 * (n : ℝ)) ^ ((3 : ℝ) / 4) *
      Real.sqrt (R ^ 3 / (d * L * (3 + R / r) * G)))
    (hδr : δ ≤ r) :
    pseudoRegret K ℓ P (fun t ω => x t ω + δ • S t ω) n ≤
      4 * (n : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt (R * d * L * (3 + R / r) * G) := by sorry

end RegretBandits.Nonlinear
