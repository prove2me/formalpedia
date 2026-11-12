-- Prove2me | Theorems.Thm_RegAggregation_Posterior_inverse_gamma_integral
-- name    : RegAggregation.Posterior.inverse_gamma_integral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:48.625648+00:00
-- url     : https://prove2.me/theorems/10b1d391-65db-49ee-ad4f-9c3e37cd2b6f
-- title:
--   Proof of Theorem 3.3, p. 41 — ∫₀^∞ x^{−(s+1)} e^{−c/x} dx = Γ(s) c^{−s} (inverse gamma normalizer)
-- statement:
--   Let $s>0$ and $c>0$. Then
--   $$\int_0^\infty x^{-(s+1)} e^{-c/x}\,dx = \Gamma(s)\,c^{-s}.$$
--   Equivalently, $x\mapsto \frac{c^s}{\Gamma(s)}x^{-(s+1)}e^{-c/x}$ is the density of the inverse gamma distribution $\Gamma^{-1}(s,c)$ with shape $s$ and scale $c$.
--
--   The proof of Theorem 3.3 (iii) uses this normalizing constant to integrate out $\lambda_2 = \delta-\rho$, with shape $(K-3)/2+b$ in the proof's parametrization. It is used again for the behaviour as $\lambda_1 \downarrow 0$.
--
--   **Formalization Note** The integral is the Lebesgue integral of a nonnegative function, taken in $[0,\infty]$ (`lintegral`). The statement asserts in particular that it is finite.
-- source:
--   Satopää, Regularized Aggregation of One-off Probability Predictions, SSRN working paper 3769945 (version of 2021-08-10; published in Operations Research 2022), p. 41, proof of Theorem 3.3 (iii)

import Mathlib
import Definitions.Def_RegAggregation_Posterior_Model

namespace RegAggregation.Posterior

theorem inverse_gamma_integral (s c : ℝ) (hs : 0 < s) (hc : 0 < c) :
    ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x ^ (-(s + 1)) * Real.exp (-c / x)) =
      ENNReal.ofReal (Real.Gamma s * c ^ (-s)) := by sorry

end RegAggregation.Posterior
