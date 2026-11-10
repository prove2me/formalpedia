-- Prove2me | Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_9
-- name    : PrivateAgnosticHalfspace.Gaussian.lemma_B_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:24:53.666627+00:00
-- url     : https://prove2.me/theorems/b3aad6c2-8ca7-448a-987c-cd3248265667
-- title:
--   Lemma B.9 — Mehler’s formula
-- statement:
--   Let $h_\kappa$ be the normalized tensor Hermite polynomials on $\mathbb R^d$. For every $x,y\in\mathbb R^d$ and every real $\rho\in(-1,1)$, the multi-index series converges and has sum
--   $$
--   \sum_{\kappa\in\mathbb N_0^d}\rho^{|\kappa|}h_\kappa(x)h_\kappa(y)
--   =(1-\rho^2)^{-d/2}
--   \exp\!\left(\frac{2\rho\langle x,y\rangle-\rho^2(\|x\|_2^2+\|y\|_2^2)}{2(1-\rho^2)}\right).
--   $$
--   Negative $\rho$ is included. The real power on the right has positive base because $|\rho|<1$.
--
--   This supplies the pointwise Hermite kernel identity used by the feature-norm calculation.
--
--   Differences from the source:
--   - encoding: an infinite convergent multi-index series → HasSum over all natural coordinate multi-indices and real exponentiation on the positive base; reason: records convergence as well as the equality; no sign restriction on rho beyond the source interval is added
-- source:
--   Giorgio Racca, Amartya Sanyal, Vikrant Singhal, STOC 2027 submission #1006 (October 2026), p. 22, Lemma B.9; canonical PDF sha256 f0122a33e29daa624b530bdd0b071998d8e44197b30449b0cb3213289645cec7

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivateAgnosticHalfspace.Gaussian

theorem lemma_B_9 (d : ℕ) (x y : Vec d) (ρ : ℝ) (hρ : -1 < ρ ∧ ρ < 1) :
    HasSum (fun κ : Fin d → ℕ => ρ ^ degree κ * hermite d κ x * hermite d κ y)
      ((1 - ρ ^ 2) ^ (-(d : ℝ) / 2) *
        Real.exp ((2 * ρ * inner ℝ x y - ρ ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2)) /
          (2 * (1 - ρ ^ 2)))) := by sorry

end PrivateAgnosticHalfspace.Gaussian
