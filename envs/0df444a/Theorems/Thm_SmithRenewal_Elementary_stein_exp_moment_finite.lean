-- Prove2me | Theorems.Thm_SmithRenewal_Elementary_stein_exp_moment_finite
-- name    : SmithRenewal.Elementary.stein_exp_moment_finite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:01.377991+00:00
-- url     : https://prove2.me/theorems/1a2d6bb6-75ae-48f1-9a6c-d7e18e578749
-- title:
--   §1.2, p. 245 — Stein's result: E exp(θN_t) < ∞ for θ ≤ θ₀, so N_t has finite moments of all orders
-- statement:
--   Let $(X_i)$ be a renewal process with counting variable $N_t$ (the number of $n \ge 1$ with $S_n \le t$). Then:
--
--   1. for every $t$, $N_t < \infty$ almost surely;
--   2. there is a real number $\theta_0 > 0$ such that for every $t$ and every real $\theta \le \theta_0$,
--   $$\mathbb E\, e^{\theta N_t} < \infty;$$
--   3. for every $t$ and every $k \in \mathbb N$, $\mathbb E N_t^k < \infty$; in particular $H(t) = \mathbb E N_t < \infty$.
--
--   This is Stein's (1946) result specialised to renewal processes, which Smith proves by comparing $N_t$ with a negative binomial count. The finiteness of $H(t)$ is what makes the renewal function a real-valued object.
--
--   **Formalization Note** The exponential moment is taken of `(N_t).toNat`, legitimate because of item 1. The paper allows complex $\theta$ with real part at most $\theta_0$; since $|e^{\theta N_t}| = e^{(\operatorname{Re}\theta) N_t}$, the real case carries the whole content. $\theta_0$ is chosen independently of $t$, which is what the paper's comparison argument provides.
-- source:
--   Smith, Renewal Theory and Its Ramifications, J. R. Statist. Soc. B 20(2):243–283 (1958), DOI 10.1111/j.2517-6161.1958.tb00294.x, §1.2, p. 245, Stein's result and its simpler proof

import Mathlib
import Definitions.Def_SmithRenewal_Elementary_RenewalProcess

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SmithRenewal.Elementary

/-- Stein's result for renewal processes (Smith, *Renewal Theory and Its Ramifications*, J. R.
Statist. Soc. B 20(2):243–283 (1958), §1.2, p. 245, unnumbered): "there is a real number θ₀ > 0
such that the generating function E{exp (θN_t)} exists for any θ whose real part is less than or
equal to θ₀, and an immediate consequence of this result is that N_t has finite moments of all
orders", proved for renewal processes by the comparison with a negative binomial count on the same
page.

Formalization Note: `N_t` is a.s. finite (first conjunct), so `E exp(θ N_t)` is taken of
`(N_t).toNat`. Only real `θ` is stated: for complex `θ`, `|exp(θ N_t)| = exp((Re θ) N_t)`, so
existence for real `θ ≤ θ₀` is the whole content. The `θ₀` is chosen uniformly in `t`, which is
what the paper's comparison argument gives (any `0 < θ₀ < −log(1 − β)`). Moments are lower
integrals in `[0, ∞]`; `k = 1` gives `H(t) < ∞`. -/
theorem stein_exp_moment_finite {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX : IsRenewalProcess P X) :
    (∀ t : ℝ, ∀ᵐ ω ∂P, N X t ω ≠ ⊤) ∧
    (∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ t : ℝ, ∀ θ : ℝ, θ ≤ θ₀ →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * ((N X t ω).toNat : ℝ))) ∂P < ∞) ∧
    (∀ t : ℝ, ∀ k : ℕ, ∫⁻ ω, (N X t ω : ℝ≥0∞) ^ k ∂P < ∞) := by sorry

end SmithRenewal.Elementary
