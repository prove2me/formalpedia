-- Prove2me | Theorems.Thm_ShorNonsmooth_Stochastic_conditional_one_step
-- name    : ShorNonsmooth.Stochastic.conditional_one_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T12:53:04.17495+00:00
-- url     : https://prove2.me/theorems/e28554ec-8aa4-49db-8e89-83a73f8c4c8d
-- title:
--   Eq. (2.42) — $E\{\|x_{k+1}-x^*\|^2 / x_k\} \le \|x_k - x^*\|^2 + c\,h_k^2(x_k)$
-- statement:
--   Let $f : E_n \to \mathbb{R}$ be convex and let $x^*$ be a minimum point of $f$. Let $(\Omega, \mathcal F, P)$ be a probability space with a filtration $(\mathcal F_k)_{k \ge 0}$, and let $x_k$ be the stochastic subgradient method $x_{k+1} = x_k - h_k(x_k)\, g_k$ started at a deterministic $x_0$, where each stepsize rule $h_j$ is Borel measurable and each random direction $g_j$ is $\mathcal F_{j+1}$-measurable (so $x_k$ is $\mathcal F_k$-measurable).
--
--   Fix an iteration $k$ and assume:
--
--   1. $g_k$ and $\|g_k\|^2$ are integrable, $E\{g_k \mid \mathcal F_k\}$ is almost surely a subgradient of $f$ at $x_k$, and $E\{\|g_k\|^2 \mid \mathcal F_k\} \le c$ almost surely;
--   2. the stepsize rule satisfies $0 < h_k(y) \le B$ for all $y \in E_n$;
--   3. $\|x_k - x^*\|^2$ is integrable.
--
--   Then $\|x_{k+1} - x^*\|^2$ is integrable and, almost surely,
--   $$
--   E\{\|x_{k+1} - x^*\|^2 \mid \mathcal F_k\} \le \|x_k - x^*\|^2 + c\, h_k^2(x_k).
--   $$
--
--   This is the one-step inequality on which the supermartingale argument for Theorem 2.19 rests.
--
--   **Formalization Note** The book conditions on $x_k$; here the conditioning is on $\mathcal F_k$, the information available when $x_k$ is computed, which contains $\sigma(x_k)$. The integrability of $\|x_k - x^*\|^2$ and the bound $B$ on the stepsize are added so that the conditional expectation is a genuine one (Lean's conditional expectation of a non-integrable function is $0$, which would make the inequality trivial); the integrability of $\|x_{k+1}-x^*\|^2$ is part of the conclusion. The printed display (2.42) has $\|x_k - x^*\|^2$ on its left-hand side; the preceding computation on the same page and the use made of (2.42) show that $\|x_{k+1} - x^*\|^2$ is meant, and that is what is stated.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 46, inequality (2.42) (proof of Theorem 2.19)

import Mathlib
import Definitions.Def_ShorNonsmooth_Stochastic_StochasticSubgradientMethod
open MeasureTheory Filter Topology

namespace ShorNonsmooth.Stochastic

/-- Shor (1985), p. 46, **inequality (2.42)** (proof of Theorem 2.19): one step of the stochastic
subgradient method `x_{k+1} = x_k - h_k(x_k) g_ω(x_k)` satisfies
`E{‖x_{k+1} - xstar‖² | ℱ k} ≤ ‖x_k - xstar‖² + c h_k(x_k)²` a.s., where `xstar` is a minimum
point of `f`. The conditioning σ-algebra `ℱ k` plays the role of the book's conditioning on
`x_k`. So that the conditional expectation is not Lean's junk value `0`, the statement assumes
`‖x_k - xstar‖²` integrable and the stepsize rule `h k` positive and bounded by `B` at this
step, and concludes that `‖x_{k+1} - xstar‖²` is integrable as well. -/
theorem conditional_one_step {n : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : xstar ∈ ShorNonsmooth.SubgradMethod.MinSet f)
    (h : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hh_meas : ∀ j, Measurable (h j))
    (G : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (x₀ : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hG_meas : ∀ j, StronglyMeasurable[ℱ (j + 1)] (G j)) (k : ℕ)
    (hG_int : Integrable (G k) μ)
    (hG_sq_int : Integrable (fun ω => ‖G k ω‖ ^ 2) μ)
    (hG_mean : ∀ᵐ ω ∂μ, ShorNonsmooth.AlmostDiff.IsSubgradient f (stochIter h G x₀ k ω) ((μ[G k | ℱ k]) ω))
    (hG_sq : ∀ᵐ ω ∂μ, (μ[fun ω' => ‖G k ω'‖ ^ 2 | ℱ k]) ω ≤ c)
    (B : ℝ) (hh_pos : ∀ y, 0 < h k y) (hh_bdd : ∀ y, h k y ≤ B)
    (hx_int : Integrable (fun ω => ‖stochIter h G x₀ k ω - xstar‖ ^ 2) μ) :
    Integrable (fun ω => ‖stochIter h G x₀ (k + 1) ω - xstar‖ ^ 2) μ ∧
      μ[fun ω => ‖stochIter h G x₀ (k + 1) ω - xstar‖ ^ 2 | ℱ k] ≤ᵐ[μ]
        fun ω => ‖stochIter h G x₀ k ω - xstar‖ ^ 2 + c * h k (stochIter h G x₀ k ω) ^ 2 := by sorry

end ShorNonsmooth.Stochastic
