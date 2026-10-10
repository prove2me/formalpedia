-- Prove2me | Theorems.Thm_PriceQualityService_Joint_quality_step
-- name    : PriceQualityService.Joint.quality_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:22:50.539792+00:00
-- url     : https://prove2.me/theorems/204689eb-0e52-41c1-afd5-54befc432d93
-- title:
--   Quality step (18): each summand is maximized at $q_i=(\alpha_i+t_ib_i)/(2c_i)$
-- statement:
--   Fix a product $i$ with $c_i>0$, a service duration $\tau$ for it and a real number $r$. The function
--   $$
--   g(x)=\exp\bigl(\alpha_ix-c_ix^2+\tau(s_i-(a_i-b_ix))-r-1\bigr),
--   $$
--   which is the $i$-th summand of the right-hand side of (18) as a function of the quality $x=q_i$, attains its maximum exactly at
--   $$
--   \bar q_i=\frac{\alpha_i+\tau b_i}{2c_i},
--   $$
--   (at no other point), and its maximum value is
--   $$
--   g(\bar q_i)=\exp\Bigl(\frac{b_i^2\tau^2}{4c_i}+\Bigl(s_i-a_i+\frac{\alpha_ib_i}{2c_i}\Bigr)\tau+\frac{\alpha_i^2}{4c_i}-r-1\Bigr).
--   $$
--   Because the right-hand side of (18) is a sum of such terms, one per product, the quality of each product is optimized independently of the others; the maximum value is the summand $h_i(r,t_i)$ of (19).
--
--   **Formalization Note** $c_i>0$ is the paper's assumption that the production cost $c_iq_i^2$ is increasing and convex in quality (p. 8); it is not written in the proof. Qualities range over $\mathbb R$; the model's range $[0,a_i/b_i)$ is not imposed.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), p. 26, Appendix B, Proof of Theorem 1, eq. (18) and the definition of $h_i(r,t_i)$ in (19)

import Mathlib
import Definitions.Def_PriceQualityService_Joint_Model

namespace PriceQualityService.Joint

/-- Quality step, (18), Appendix B, Proof of Theorem 1, p. 26: for `c_i > 0`, a duration `τ` of
product `i` and any `r`, the summand
`x ↦ exp(α_i x − c_i x² + τ(s_i − (a_i − b_i x)) − r − 1)` of the right-hand side of (18) is
maximized exactly at `x = (α_i + τ b_i)/(2c_i)`, where it equals the summand of (19),
`exp(b_i² τ²/(4c_i) + (s_i − a_i + α_i b_i/(2c_i)) τ + α_i²/(4c_i) − r − 1)`. -/
theorem quality_step {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (i : Fin N) (τ r : ℝ) :
    let g : ℝ → ℝ := fun x =>
      Real.exp (α i * x - c i * x ^ 2 + τ * (s i - (a i - b i * x)) - r - 1)
    let qbar : ℝ := (α i + τ * b i) / (2 * c i)
    (∀ x : ℝ, g x ≤ g qbar) ∧ (∀ x : ℝ, g x = g qbar → x = qbar) ∧
      g qbar = Real.exp (durationExponent α a b c s i τ - r - 1) := by sorry

end PriceQualityService.Joint
