-- Prove2me | Theorems.Thm_PriceQualityService_Uniform_equation_24
-- name    : PriceQualityService.Uniform.equation_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:38.568986+00:00
-- url     : https://prove2.me/theorems/ad4cdfe0-68fd-4332-8291-2f88794d15ad
-- title:
--   (24): at a uniform duration $t$ the optimal profit is the unique root of $r=\sum_i G_i(r,t)$
-- statement:
--   Let $c_i>0$ for every product and fix a common service duration $t\in\mathbb R$ for all products, so that $t_i=t$ for every $i\in\mathcal N$. Write
--   $$
--   G_i(r,t)=\exp\Big(\frac{b_i^2t^2}{4c_i}+\Big(s_i-a_i+\frac{\alpha_ib_i}{2c_i}\Big)t+\frac{\alpha_i^2}{4c_i}-r-1\Big).
--   $$
--   Then:
--
--   1. the equation $r=\sum_{i\in\mathcal N}G_i(r,t)$ has exactly one real solution $r$;
--   2. for this $r$, every price vector $\mathbf p\in\mathbb R^N$ and quality vector $\mathbf q\in\mathbb R^N$ satisfy $\Pi(\mathbf p,\mathbf q,(t,\dots,t);\mathcal N)\le r$;
--   3. the value $r$ is attained at
--   $$
--   q_i=\frac{\alpha_i+tb_i}{2c_i},\qquad p_i=1+r+c_iq_i^2+t(a_i-b_iq_i)\qquad(i\in\mathcal N).
--   $$
--
--   This is the reduction (24) of the uniform-duration problem (7) to a single variable: for each uniform duration the optimal price–quality profit is the root of a scalar equation, so optimizing over $t$ means optimizing that root.
--
--   **Formalization Note** The statement holds for every real $t$, not only $t\in[t_s,t_l]$. Prices and qualities range over all of $\mathbb R^N$; the model's normalization $q_i\in[0,a_i/b_i)$ (p. 8) is not imposed, as in the paper's first-order derivation. The uniform duration vector is the constant function `fun _ => t`.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), p. 29, Proof of Theorem 3, (24)

import Mathlib
import Definitions.Def_PriceQualityService_Joint_Model
import Definitions.Def_PriceQualityService_Uniform_Reduction

namespace PriceQualityService.Uniform

open Finset

/-- (24), Proof of Theorem 3, Wang, Ke & Cui, accepted manuscript (SSRN 3766191), p. 29. Fix a
common service duration `t` for all products. The equation
`r = ∑_i exp(b_i² t²/(4c_i) + (s_i − a_i + α_i b_i/(2c_i)) t + α_i²/(4c_i) − r − 1)` has exactly one
real root, and for that root `r` the optimal profit over all prices and qualities at the uniform
duration `t` equals `r`: every `(p, q)` earns at most `r`, and `r` is earned at
`q_i = (α_i + t b_i)/(2c_i)`, `p_i = 1 + r + c_i q_i² + t (a_i − b_i q_i)`.
Prices and qualities range over all of `ℝ^N`. -/
theorem equation_24 {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (t : ℝ) :
    (∃! r : ℝ, r = ∑ i, gTerm α a b c s r t i) ∧
    ∀ r : ℝ, r = ∑ i, gTerm α a b c s r t i →
      (∀ p q : Fin N → ℝ, PriceQualityService.Joint.profit α a b c s p q (fun _ => t) ≤ r) ∧
      PriceQualityService.Joint.profit α a b c s
        (fun i => 1 + r + c i * ((α i + t * b i) / (2 * c i)) ^ 2
          + t * (a i - b i * ((α i + t * b i) / (2 * c i))))
        (fun i => (α i + t * b i) / (2 * c i)) (fun _ => t) = r := by sorry

end PriceQualityService.Uniform
