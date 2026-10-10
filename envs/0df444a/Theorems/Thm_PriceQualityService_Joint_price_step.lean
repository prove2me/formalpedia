-- Prove2me | Theorems.Thm_PriceQualityService_Joint_price_step
-- name    : PriceQualityService.Joint.price_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:22:27.162645+00:00
-- url     : https://prove2.me/theorems/476e28c8-8259-42c2-9112-8f52f699b3f1
-- title:
--   Price step: $h_i(r,p_i)$ is maximized at $p_i=1+c_iq_i^2+t_i(a_i-b_iq_i)+r$
-- statement:
--   Fix a product $i$, its quality $q_i$ and duration $t_i$, and a real number $r$. Consider, as a function of the price $p_i$,
--   $$
--   h_i(r,p_i)=\bigl[p_i-c_iq_i^2-t_i(a_i-b_iq_i)-r\bigr]\cdot\exp(\alpha_iq_i-p_i+t_is_i).
--   $$
--   Let $\bar p_i=1+c_iq_i^2+t_i(a_i-b_iq_i)+r$. Then $h_i(r,\cdot)$ is strictly increasing on $(-\infty,\bar p_i]$, strictly decreasing on $[\bar p_i,\infty)$, and its maximum value is
--   $$
--   h_i(r,\bar p_i)=\exp\bigl(\alpha_iq_i-c_iq_i^2+t_i(s_i-(a_i-b_iq_i))-r-1\bigr).
--   $$
--   This is the price step of the proof of Theorem 1: given $r$, each product's price maximizes its own term of the fixed-point form (15), and the optimal markup is $1+r$ for every product.
--
--   **Formalization Note** The paper says "increasing … and decreasing thereafter"; the statement uses the strict forms, which hold because the derivative $[1-(p_i-c_iq_i^2-t_i(a_i-b_iq_i)-r)]\exp(\cdot)$ vanishes only at $\bar p_i$. No sign assumption on any parameter is needed.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), p. 26, Appendix B, Proof of Theorem 1, display after (16)

import Mathlib
import Definitions.Def_PriceQualityService_Joint_Model

namespace PriceQualityService.Joint

/-- Price step, Appendix B, Proof of Theorem 1, p. 26: for fixed `r`, quality `q` and durations `t`,
`h_i(r, p_i) = [p_i − c_i q_i² − t_i(a_i − b_i q_i) − r] · exp(α_i q_i − p_i + t_i s_i)` increases in
`p_i` for `p_i ≤ 1 + c_i q_i² + t_i(a_i − b_i q_i) + r`, decreases thereafter, and its maximum is
`exp(α_i q_i − c_i q_i² + t_i(s_i − (a_i − b_i q_i)) − r − 1)`, attained at that price. -/
theorem price_step {N : ℕ} (α a b c s q t : Fin N → ℝ) (i : Fin N) (r : ℝ) :
    let h : ℝ → ℝ := fun x =>
      (x - c i * q i ^ 2 - t i * (a i - b i * q i) - r) * Real.exp (α i * q i - x + t i * s i)
    let pbar : ℝ := 1 + c i * q i ^ 2 + t i * (a i - b i * q i) + r
    StrictMonoOn h (Set.Iic pbar) ∧ StrictAntiOn h (Set.Ici pbar) ∧
      h pbar = Real.exp (α i * q i - c i * q i ^ 2 + t i * (s i - (a i - b i * q i)) - r - 1) ∧
      ∀ x : ℝ, h x ≤ h pbar := by sorry

end PriceQualityService.Joint
