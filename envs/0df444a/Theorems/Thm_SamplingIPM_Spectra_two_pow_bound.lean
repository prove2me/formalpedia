-- Prove2me | Theorems.Thm_SamplingIPM_Spectra_two_pow_bound
-- name    : SamplingIPM.Spectra.two_pow_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:47.240066+00:00
-- url     : https://prove2.me/theorems/c47b2da5-e9c5-4977-92f7-a65f122df88c
-- title:
--   Proof of Theorem 3.1, p. 12 — ‖θ_m‖ ≤ 1/(4R) and 2^{−m−2} ≥ (1/8)(4R‖θ‖)^{−2√ϑ−1}
-- statement:
--   Let $R>0$, $\vartheta>0$ and $\theta\in\mathbb R^n$ with $\|\theta\|>\frac1{4R}$. Put $t=\frac1{2\sqrt\vartheta+1}\in(0,1)$,
--   $$\theta_k=(1-t)^k\theta,\qquad m=\left\lceil\frac{\log_2\big(\frac1{4R\|\theta\|}\big)}{\log_2(1-t)}\right\rceil .$$
--   Then
--
--   1. $\|\theta_m\|\le\frac1{4R}$;
--   2. $2^{-m-2}\ \ge\ \frac18\,(4R\|\theta\|)^{1/\log_2(1-t)}$;
--   3. $\frac18\,(4R\|\theta\|)^{1/\log_2(1-t)}\ \ge\ \frac18\,(4R\|\theta\|)^{-2\sqrt\vartheta-1}$.
--
--   Together,
--   $$2^{-m-2}\ \ge\ \frac18\,(4R\|\theta\|)^{1/\log_2(1-\frac1{2\sqrt\vartheta+1})}\ \ge\ \frac18\,(4R\|\theta\|)^{-2\sqrt\vartheta-1}.$$
--
--   These are the elementary estimates that turn the halving chain (15) and the small-parameter bound (14) into the explicit second bound of Theorem 3.1.
--
--   **Formalization Note** $0<R$ and $0<\vartheta$ are stated explicitly because this statement has no convex body: in the paper $R>0$ follows from $K$ having non-empty interior, and $\vartheta>0$ is the paper's "$t\in(0,1)$". The powers with real exponents are real powers of a base larger than one; $2^{-m-2}$ is an integer power.
-- source:
--   Badenbroek & de Klerk, Complexity Analysis of a Sampling-Based Interior Point Method for Convex Optimization, arXiv:1811.07677v1, p. 12, proof of Theorem 3.1 (choice of m and the lower bound for 2^{−m−2})

import Mathlib
import Definitions.Def_SamplingIPM_Spectra_Model

namespace SamplingIPM.Spectra

theorem two_pow_bound {n : ℕ} (R ϑ : ℝ) (hR : 0 < R) (hϑ0 : 0 < ϑ)
    (θ : EuclideanSpace ℝ (Fin n)) (hθ : 1 / (4 * R) < ‖θ‖) :
    ‖thetaSeq ϑ θ (mSteps R ϑ θ)‖ ≤ 1 / (4 * R) ∧
      (1 / 8) * (4 * R * ‖θ‖) ^ (1 / Real.logb 2 (1 - 1 / (2 * Real.sqrt ϑ + 1)))
          ≤ (2 : ℝ) ^ (-(mSteps R ϑ θ : ℤ) - 2) ∧
      (1 / 8) * (4 * R * ‖θ‖) ^ (-2 * Real.sqrt ϑ - 1)
          ≤ (1 / 8) * (4 * R * ‖θ‖) ^ (1 / Real.logb 2 (1 - 1 / (2 * Real.sqrt ϑ + 1))) := by sorry

end SamplingIPM.Spectra
