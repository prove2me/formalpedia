-- Prove2me | Theorems.Thm_RegretBandits_Nonlinear_osgd_two_point_regret_tuned
-- name    : RegretBandits.Nonlinear.osgd_two_point_regret_tuned
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:42:44.760181+00:00
-- url     : https://prove2.me/theorems/ad4e42c0-de3b-482e-9953-c4052983f4e4
-- title:
--   Theorem 6.1 (second display) — OSGD with two-point feedback, η = R/(Gd√n)
-- statement:
--   In the setting of Theorem 6.1 ($d\ge1$; $\mathcal K$ closed and convex with $r\,\mathbb B\subseteq\mathcal K\subseteq R\,\mathbb B$, $r,R>0$; a fixed sequence of $G$-Lipschitz, differentiable, convex losses; OSGD on $(1-\delta/r)\mathcal K$ with the two-point estimates (6.1); independent uniform directions $S_t$ and independent fair signs choosing the played point $\widetilde X_t\in\{X_t^+,X_t^-\}$), assume $G>0$, $n\ge1$, $0<\delta\le r$ and
--   $$\eta=\frac{R}{Gd\sqrt n}.$$
--   Then
--   $$\overline R_n\le 2RGd\sqrt n+\delta\Big(3+\frac Rr\Big)Gn .$$
--   Letting $\delta\to0$ gives the book's $\overline R_n\le 2RGd\sqrt n$.
--
--   **Formalization Note** Corrected misprint: the book prints $\eta=R/(GD\sqrt n)$, where $D$ is undefined and means $d$, and states "$\overline R_n\le 2RGd\sqrt n$ for $\delta\to0$", a limit over different runs. This item states the explicit inequality, valid for every admissible $\delta$, that the first display gives with this $\eta$ and that implies the limit. Added hypothesis $\delta\le r$ as in Theorem 6.1, and $G>0$, $n\ge1$ so that $\eta$ is defined.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 93, Theorem 6.1 (second display)

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_Smoothing
import Definitions.Def_RegretBandits_Nonlinear_OSGD

open MeasureTheory ProbabilityTheory
open scoped NNReal Pointwise

namespace RegretBandits.Nonlinear

/-- Theorem 6.1, second display (Bubeck, Cesa-Bianchi, arXiv:1204.5721v2, p. 93), in the explicit
form the first display gives. In the setting of Theorem 6.1 (`d ≥ 1`, `K` closed convex with
`r𝔹 ⊆ K ⊆ R𝔹`, `G`-Lipschitz differentiable convex losses, OSGD on `(1 - δ/r)K` with the
two-point estimates (6.1), independent uniform directions `S_t` and fair signs `C_t`, played
point `X̃_t = x_t + C_t δ S_t`), assume `G > 0`, `n ≥ 1`, `0 < δ ≤ r` and `η = R/(Gd√n)`. Then
`R̄_n ≤ 2RGd√n + δ(3 + R/r)Gn`. Corrected misprint: the book prints `η = R/(GD√n)` (`D` is
`d`) and states the limit `R̄_n ≤ 2RGd√n` "for `δ → 0`"; the explicit inequality for every
admissible `δ` implies that limit. -/
theorem osgd_two_point_regret_tuned
    {d : ℕ} (hd : 1 ≤ d)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hKclosed : IsClosed K) (hKconv : Convex ℝ K)
    (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (hrK : Metric.closedBall 0 r ⊆ K) (hKR : K ⊆ Metric.closedBall 0 R)
    (G : ℝ≥0) (ℓ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hℓlip : ∀ t, LipschitzWith G (ℓ t)) (hℓdiff : ∀ t, Differentiable ℝ (ℓ t))
    (hℓconv : ∀ t, ConvexOn ℝ Set.univ (ℓ t))
    (hG : 0 < G) (δ η : ℝ) (hδ : 0 < δ) (hδr : δ ≤ r)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (C : ℕ → Ω → ℝ)
    (hSm : ∀ t, Measurable (S t)) (hCm : ∀ t, Measurable (C t))
    (hind : iIndepFun (fun t ω => (S t ω, C t ω)) P)
    (hlaw : ∀ t, P.map (fun ω => (S t ω, C t ω)) = (uniformSphere d).prod fairSign)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hx : ∀ ω, IsOSGDRun ((1 - δ / r) • K) η
      (fun t y => twoPointEstimate d δ (ℓ t) (S t ω) y) (fun t => x t ω))
    (n : ℕ)
    (hn : 0 < n) (hηdef : η = R / ((G : ℝ) * d * Real.sqrt n)) :
    pseudoRegret K ℓ P (fun t ω => x t ω + (C t ω * δ) • S t ω) n ≤
      2 * R * G * d * Real.sqrt n + δ * (3 + R / r) * G * n := by sorry

end RegretBandits.Nonlinear
