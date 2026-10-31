-- Prove2me | Theorems.Thm_RetailTheft_lemma_EC1
-- name    : RetailTheft.lemma_EC1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:14:12.269993+00:00
-- url     : https://prove2.me/theorems/085a9d43-ea29-4a2b-a6b3-cbe94e10fc04
-- title:
--   Lemma EC.1 — $g$ of (EC.25) has at most one zero in $(\lambda_2,\theta/(1+\theta))$
-- statement:
--   Let $b>1$, $0<\alpha\le1$ and $0\le\theta<1$, and let $g$ be the function (EC.25),
--   $$
--   g(\lambda)=\frac{\big(\theta^2/\lambda^2-(1+\theta)^2\big)\,2(1-b^2)\alpha(1-\lambda)}{\sqrt{\rho(\lambda)}}+b(1+\alpha)+\sqrt{\rho(\lambda)},\qquad \rho(\lambda)=b^2(1+\alpha)^2+4(1-b^2)\alpha(1-\lambda)\big[(1+\theta)^2-\theta^2/\lambda\big].
--   $$
--   Then $g$ has at most one zero in the open interval $(\lambda_2,\theta/(1+\theta))$.
--
--   Up to a positive factor, $g$ is the derivative of the third-scenario price of Proposition EC.3 in $\lambda$; this lemma locates the turning point $\bar\lambda$ of the optimal price in Theorem 2.
--
--   Differences from the source:
--   - reading: uniform-instance parameters b > 1, α ≤ 1, θ ∈ [0,1) → b > 1, 0 < α ≤ 1, 0 ≤ θ < 1; reason: α > 0 makes λ₂ (which divides by α) and the uniform law meaningful
-- source:
--   Chen–Tian–Zuo, Optimal Capacity and Price Designs Under Ex Ante and Ex Post Theft, MSOM (2025), doi:10.1287/msom.2025.0024, e-companion, Lemma EC.1 and (EC.25), p. ec12 (PDF 45); proof p. ec13

import Mathlib
import Definitions.Def_RetailTheft_Uniform

namespace RetailTheft

/-- **Lemma EC.1** of Chen, Tian and Zuo, *Optimal Capacity and Price Designs Under Ex Ante and Ex
Post Theft*, MSOM (2025), doi:10.1287/msom.2025.0024, e-companion, p. ec12 (PDF 45); proof
p. ec13. The function `g` of (EC.25) has at most one zero in the open interval
`(λ₂, θ/(1 + θ))`.

**Formalization Note** The parameters are those of the uniform instance of §4.2: `b > 1`,
`0 < α ≤ 1`, `0 ≤ θ < 1`. On `(λ₂, θ/(1 + θ))` one has `λ > 0` and the radicand of `g` is
positive, so the square root and the divisions in `g` are the paper's. -/
theorem lemma_EC1 (b α θ : ℝ) (hb : 1 < b) (hα0 : 0 < α) (hα1 : α ≤ 1) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) :
    {lam : ℝ | lam ∈ Set.Ioo (lam2 b α θ) (θ / (1 + θ)) ∧ g b α θ lam = 0}.Subsingleton := by sorry

end RetailTheft
