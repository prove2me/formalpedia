-- Prove2me | Theorems.Thm_SAARate_SharpLD_display_3_14
-- name    : SAARate.SharpLD.display_3_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:06.208995+00:00
-- url     : https://prove2.me/theorems/d6af3281-df99-4774-a0bc-feb0f446ed2c
-- title:
--   (3.14), p. 12 — I_d(0) ≥ c²/(2κ²) for all d ∈ T_Θ(x̄) ∩ S^{m−1}
-- statement:
--   Let $P$ be a probability measure on a measurable space $(\Omega,\mathcal F)$, let $h:\mathbb R^m\times\Omega\to\mathbb R$, and let $\Theta\subseteq\mathbb R^m$. Write $f(x)=\mathbb E_P\,h(x,\omega)$ for the true objective (1.1) and $\hat f_N(x)=N^{-1}\sum_{j=1}^N h(x,\omega^j)$ for the sample average objective (1.2) built from an i.i.d. sample $\omega^1,\omega^2,\dots$ with law $P$. The assumptions of Theorem 2.1 are: (i) $h(\cdot,\omega)$ is convex for every $\omega$; (ii) $f$ is well defined and finite valued; (iii) $\Theta$ is closed and convex; (iv) Assumption (A): $f$ has the unique minimizer $\bar x$ on $\Theta$ and there is $c>0$ with $f(x)\ge f(\bar x)+c\|x-\bar x\|$ for all $x\in\Theta$. Assumption (B) asks for a $\kappa>0$ with $\sup_{d\in S^{m-1}}|h'_\omega(\bar x,d)|\le\kappa$ for $P$-almost every $\omega$, where $h'_\omega(\bar x,d)$ is the directional derivative of $h(\cdot,\omega)$ at $\bar x$ in direction $d$ and $S^{m-1}$ is the unit sphere.
--
--   Suppose (i)–(iv) hold, that $c>0$ satisfies $f(x)\ge f(\bar x)+c\|x-\bar x\|$ for all $x\in\Theta$ (2.2), and that Assumption (B) holds with constant $\kappa$. For a direction $d$ let $I_d(\alpha)=\sup_{t\in\mathbb R}[t\alpha-\log\mathbb E_P e^{t\eta(d,\omega)}]$ be the rate function (3.5) of $\eta(d,\omega)=h'_\omega(\bar x,d)$. Then
--   $$I_d(0)\ge\frac{c^2}{2\kappa^2}\qquad\text{for all } d\in T_\Theta(\bar x)\cap S^{m-1}.$$
--
--   Each one-dimensional projection of $\zeta_N=\hat f'_N(\bar x,\cdot)$ along a feasible unit direction is unlikely to be non-positive, at the explicit rate $c^2/(2\kappa^2)$.
--
--   **Formalization Note** "f finite valued" is the hypothesis that $h(x,\cdot)$ is $P$-integrable for every $x$ (it includes measurability). $I_d$ is the published extended-real `legendre (logMGF P X)`. The constant $c$ is a separate binder together with (2.2); Assumption (A) supplies some such constant, and the statement holds for every one. The i.i.d. sample plays no role and is omitted. The tangent cone is Mathlib's `tangentConeAt`, equal for convex $\Theta$ to the closure of the cone of feasible directions.
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), p. 12, proof of Theorem 3.1, (3.14), with (2.2), (3.1), (3.5), Assumptions (A), (B)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation
import Definitions.Def_SAARate_SharpLD_Setting

open MeasureTheory ProbabilityTheory Filter Topology BellWilliams2001.ThresholdPolicy

namespace SAARate.SharpLD

theorem display_3_14 {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : SAARate.Sharp.E m → Ω → ℝ)
    (hconv : ∀ ω, ConvexOn ℝ Set.univ (fun x => h x ω))
    (hint : ∀ x, Integrable (h x) P)
    (Θ : Set (SAARate.Sharp.E m)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ)
    (xbar : SAARate.Sharp.E m) (hA : SAARate.Sharp.AssumptionA P h Θ xbar)
    (c : ℝ) (hc : 0 < c)
    (h22 : ∀ x ∈ Θ, SAARate.Sharp.expectedObj P h x ≥ SAARate.Sharp.expectedObj P h xbar + c * ‖x - xbar‖)
    (κ : ℝ) (hB : AssumptionB P h xbar κ) :
    ∀ d ∈ tangentConeAt ℝ Θ xbar ∩ Metric.sphere (0 : SAARate.Sharp.E m) 1,
      ((c ^ 2 / (2 * κ ^ 2) : ℝ) : EReal) ≤ legendre (logMGF P (eta h xbar d)) 0 := by sorry

end SAARate.SharpLD
