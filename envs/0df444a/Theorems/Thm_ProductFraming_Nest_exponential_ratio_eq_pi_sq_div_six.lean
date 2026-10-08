-- Prove2me | Theorems.Thm_ProductFraming_Nest_exponential_ratio_eq_pi_sq_div_six
-- name    : ProductFraming.Nest.exponential_ratio_eq_pi_sq_div_six
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:07:23.43496+00:00
-- url     : https://prove2.me/theorems/7a1d8589-5685-498e-bd4d-a49bb88bbcad
-- title:
--   Proof of Theorem 3, p. 37 — $\mathbb E[W/(\mu(1-e^{-W/\mu}))] = \pi^2/6$
-- statement:
--   Let $\mu>0$ and let $W$ be exponential with mean $\mu$. Then
--   $$\mathbb E\Big[\frac{W}{\mu\,(1-\exp(-W/\mu))}\Big]=\int_0^\infty\frac{(w/\mu)\exp(-w/\mu)}{1-\exp(-w/\mu)}\,\frac{dw}{\mu}=\frac{\pi^2}{6}.$$
--
--   Since $\mathbb E[\min(W,Z)\mid W]=\mu(1-\exp(-W/\mu))$ for an independent exponential $Z$ with mean $\mu$, this evaluates the right-hand side of Corollary 6 and gives $1/\gamma\le\pi^2/6$.
--
--   **Formalization Note** The law of $W$ is `expMeasure` with rate $1/\mu$. At $w=0$ the integrand is $0/0=0$ in Lean, on a null set.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, A.2, Proof of Theorem 3, p. 37 (display)

import Mathlib

namespace ProductFraming.Nest

open MeasureTheory ProbabilityTheory

/-- Proof of Theorem 3, display (Gallego, Li, Truong, Wang 2020, A.2, p. 37): for `W` exponential with
mean `μ > 0`, `E[W / (μ(1 − exp(−W/μ)))] = π²/6`. Mathlib's `expMeasure` takes the rate `μ⁻¹`. -/
theorem exponential_ratio_eq_pi_sq_div_six (μ : ℝ) (hμ : 0 < μ) :
    ∫ w, w / (μ * (1 - Real.exp (-w / μ))) ∂(expMeasure μ⁻¹) = Real.pi ^ 2 / 6 := by sorry

end ProductFraming.Nest
