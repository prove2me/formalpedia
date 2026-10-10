-- Prove2me | Theorems.Thm_PriceQualityService_Joint_duration_step
-- name    : PriceQualityService.Joint.duration_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:22:43.404024+00:00
-- url     : https://prove2.me/theorems/eb667e6a-04c8-41e5-818d-1dffdfc5dd32
-- title:
--   Duration step (19): $h_i(r,\cdot)$ is maximized over $[t_s,t_l]$ at $t_s$ or $t_l$
-- statement:
--   Fix a product $i$ with $c_i>0$, durations $t_s\le t_l$ and a real number $r$, and let
--   $$
--   h_i(r,\tau)=\exp\Bigl(\frac{b_i^2\tau^2}{4c_i}+\Bigl(s_i-a_i+\frac{\alpha_ib_i}{2c_i}\Bigr)\tau+\frac{\alpha_i^2}{4c_i}-r-1\Bigr).
--   $$
--   Then
--   $$
--   h_i(r,\tau)\le\max\{h_i(r,t_s),h_i(r,t_l)\}\qquad\text{for every }\tau\in[t_s,t_l],
--   $$
--   so the maximum of $h_i(r,\cdot)$ over the duration interval is attained at one of its endpoints. Moreover, when $b_i\ne0$, $h_i(r,\cdot)$ is strictly decreasing for $\tau\le(2(a_i-s_i)c_i-\alpha_ib_i)/b_i^2$ and strictly increasing thereafter.
--
--   This is the step of the proof of Theorem 1 that makes the optimal service duration extreme.
--
--   **Formalization Note** The endpoint bound holds for every sign of $b_i$, including $b_i=0$ (the exponent is then linear in $\tau$); the monotonicity statement, which divides by $b_i^2$, is stated only for $b_i\ne0$, as the paper's threshold requires. The paper's "decreases … and increases thereafter" is stated in strict form.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), pp. 26–27, Appendix B, Proof of Theorem 1, eq. (19) and the following paragraph

import Mathlib
import Definitions.Def_PriceQualityService_Joint_Model

namespace PriceQualityService.Joint

/-- Duration step, (19), Appendix B, Proof of Theorem 1, pp. 26–27: for `c_i > 0` and `t_s ≤ t_l`,
`h_i(r, τ) = exp(b_i² τ²/(4c_i) + (s_i − a_i + α_i b_i/(2c_i)) τ + α_i²/(4c_i) − r − 1)` attains its
maximum over `[t_s, t_l]` at an endpoint: `max_{τ∈[t_s,t_l]} h_i(r, τ) = max{h_i(r, t_s), h_i(r, t_l)}`.
For `b_i ≠ 0` it decreases for `τ ≤ (2(a_i − s_i)c_i − α_i b_i)/b_i²` and increases thereafter. -/
theorem duration_step {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (ts tl : ℝ)
    (hst : ts ≤ tl) (i : Fin N) (r : ℝ) :
    let h : ℝ → ℝ := fun τ => Real.exp (durationExponent α a b c s i τ - r - 1)
    (∀ τ ∈ Set.Icc ts tl, h τ ≤ max (h ts) (h tl)) ∧
      (b i ≠ 0 →
        StrictAntiOn h (Set.Iic ((2 * (a i - s i) * c i - α i * b i) / b i ^ 2)) ∧
          StrictMonoOn h (Set.Ici ((2 * (a i - s i) * c i - α i * b i) / b i ^ 2))) := by sorry

end PriceQualityService.Joint
