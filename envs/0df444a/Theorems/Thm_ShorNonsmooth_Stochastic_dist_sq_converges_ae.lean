-- Prove2me | Theorems.Thm_ShorNonsmooth_Stochastic_dist_sq_converges_ae
-- name    : ShorNonsmooth.Stochastic.dist_sq_converges_ae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T12:53:15.091481+00:00
-- url     : https://prove2.me/theorems/c59a2be7-b329-42eb-a848-f76645647376
-- title:
--   Theorem 2.19, proof (pp. 46–47) — $\|x_k - x^*\|^2$ converges with probability one
-- statement:
--   Let $f : E_n \to \mathbb{R}$ be convex with a minimum point $x^*$, and let $x_k$ be the stochastic subgradient method $x_{k+1} = x_k - h_k(x_k)\, g_k$ on a probability space $(\Omega, \mathcal F, P)$ with filtration $(\mathcal F_k)$, started at a deterministic $x_0$, with Borel measurable stepsize rules $h_k$ and $\mathcal F_{k+1}$-measurable directions $g_k$. Assume, for every $k$:
--
--   1. $g_k$ and $\|g_k\|^2$ are integrable, $E\{g_k \mid \mathcal F_k\}$ is almost surely a subgradient of $f$ at $x_k$, and $E\{\|g_k\|^2 \mid \mathcal F_k\} \le c$ almost surely;
--   2. almost surely, $h_k(x_k) > 0$ for all $k$ and $\sum_{k=0}^\infty h_k^2(x_k) < \infty$.
--
--   Then with probability one the limit
--   $$
--   \lim_{k \to \infty} \|x_k - x^*\|^2
--   $$
--   exists and is finite.
--
--   In the book this is the step of the proof of Theorem 2.19 where $z_k = \|x_k - x^*\|^2 + c \sum_{s \ge k} h_s^2(x_s)$ is shown to be a supermartingale; Theorem 2.19 then identifies the limit as $0$ using the divergence of $\sum h_k(x_k)$, which is not assumed here.
--
--   **Formalization Note** Conditions on the stepsizes are required almost surely, since $h_k(x_k)$ is random. The conditional bound on $\|g_k\|^2$ is the form used in (2.42).
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, pp. 46–47, proof of Theorem 2.19 (the paragraph following (2.42))

import Mathlib
import Definitions.Def_ShorNonsmooth_Stochastic_StochasticSubgradientMethod
open MeasureTheory Filter Topology

namespace ShorNonsmooth.Stochastic

/-- Shor (1985), pp. 46–47, proof of Theorem 2.19 (the step after (2.42)): the random variable
`z_k = ‖x_k - xstar‖² + c Σ_{s ≥ k} h_s²(x_s)` is a supermartingale, converges almost surely, and
hence `‖x_k - xstar‖²` converges with probability one to a finite limit. Here `xstar` is any
minimum point of the convex `f`; the divergence condition `Σ h_k(x_k) = +∞` is not assumed. -/
theorem dist_sq_converges_ae {n : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : xstar ∈ ShorNonsmooth.SubgradMethod.MinSet f)
    (h : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hh_meas : ∀ k, Measurable (h k))
    (G : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (x₀ : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hG_meas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (G k))
    (hG_int : ∀ k, Integrable (G k) μ)
    (hG_sq_int : ∀ k, Integrable (fun ω => ‖G k ω‖ ^ 2) μ)
    (hG_mean : ∀ k, ∀ᵐ ω ∂μ, ShorNonsmooth.AlmostDiff.IsSubgradient f (stochIter h G x₀ k ω) ((μ[G k | ℱ k]) ω))
    (hG_sq : ∀ k, ∀ᵐ ω ∂μ, (μ[fun ω' => ‖G k ω'‖ ^ 2 | ℱ k]) ω ≤ c)
    (hh_pos : ∀ᵐ ω ∂μ, ∀ k, 0 < h k (stochIter h G x₀ k ω))
    (hh_sq : ∀ᵐ ω ∂μ, Summable (fun k => h k (stochIter h G x₀ k ω) ^ 2)) :
    ∀ᵐ ω ∂μ, ∃ ℓ : ℝ, Tendsto (fun k => ‖stochIter h G x₀ k ω - xstar‖ ^ 2) atTop (𝓝 ℓ) := by sorry

end ShorNonsmooth.Stochastic
