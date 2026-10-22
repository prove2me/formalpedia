-- Prove2me | Theorems.Thm_RLPBidPrice_Unbiased_strong_duality_subgradient
-- name    : RLPBidPrice.Unbiased.strong_duality_subgradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T12:48:02.754992+00:00
-- url     : https://prove2.me/theorems/d508c4fb-d21b-4bf2-9ea0-b6b1e967787d
-- title:
--   §2.1, p. 211 — strong duality v(x, Y) = L(x, μ_*), μ_* is a supergradient, and a unique μ_* is the gradient
-- statement:
--   Let $A$ be a 0/1 incidence matrix with nonzero columns, $r \ge 0$, $x \ge 0$ and $Y \ge 0$, with $v$ and $L$ as above. Then:
--
--   1. an optimal dual price vector exists: some $\mu_* \ge 0$ minimizes $L(x, \cdot)$ over $\mu \ge 0$;
--   2. (strong duality and the supergradient inequality) every such minimizer $\mu_*$ satisfies $v(x, Y) = L(x, \mu_*)$ and
--   $$v(z, Y) \le v(x, Y) + \mu_*^\top (z - x) \qquad \text{for all capacity vectors } z \ge 0;$$
--   3. if the minimizer $\mu_*$ is unique and $x^i > 0$ for every $i$, then $x' \mapsto v(x', Y)$ is differentiable at $x$ with gradient $\mu_*$.
--
--   These are the facts from LP duality that turn the question of differentiability of $v$ into the uniqueness of $\mu_*$.
--
--   **Formalization Note.** The paper says "$\mu_*$ is always a subgradient of $v_k(x, Y)$"; $v$ is concave in $x$, so this is meant in the concave sense (a supergradient), stated here as the displayed inequality, over the feasible capacities $z \ge 0$. The gradient in part 3 is expressed as `HasFDerivAt` with the linear functional $h \mapsto \mu_*^\top h$; it is taken at an interior point $x > 0$. The time index $k$ is dropped.
-- source:
--   Talluri, van Ryzin, A Randomized Linear Programming Method for Computing Network Bid Prices, Transp. Sci. 33(2), 1999, p. 211, §2.1, first sentences (after Eq. (14))

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model

open MeasureTheory Matrix

namespace RLPBidPrice.Unbiased

theorem strong_duality_subgradient {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hA : IsIncidence A) (hr : 0 ≤ r) (x : Fin m → ℝ) (hx : 0 ≤ x)
    (y₀ : Fin n → ℝ) (hy₀ : 0 ≤ y₀) :
    (∃ μ, IsDualOpt A r x y₀ μ) ∧
    (∀ μ, IsDualOpt A r x y₀ μ →
      piValue A r x y₀ = lagr A r x y₀ μ ∧
      ∀ z : Fin m → ℝ, 0 ≤ z → piValue A r z y₀ ≤ piValue A r x y₀ + μ ⬝ᵥ (z - x)) ∧
    (∀ μ, IsDualOpt A r x y₀ μ → (∀ μ', IsDualOpt A r x y₀ μ' → μ' = μ) →
      (∀ i, 0 < x i) → HasFDerivAt (fun x' => piValue A r x' y₀) (gradCLM μ) x) := by sorry

end RLPBidPrice.Unbiased
