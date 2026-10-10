-- Prove2me | Theorems.Thm_PriceQualityService_Joint_eq_15
-- name    : PriceQualityService.Joint.eq_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:22:55.863431+00:00
-- url     : https://prove2.me/theorems/e9979108-330a-4a4e-b5ea-8ec31192f582
-- title:
--   (15): the MNL profit as a fixed point, $r=\sum_i[\text{markup}_i-r]\,e^{\alpha_iq_i-p_i+t_is_i}$
-- statement:
--   Let $\Pi(\mathbf p,\mathbf q,\mathbf t;\mathcal N)$ be the total expected profit of the MNL model with price, quality and service duration (equation (3)), and write $r=\Pi(\mathbf p,\mathbf q,\mathbf t;\mathcal N)$. Then for all price, quality and duration vectors,
--   $$
--   r=\sum_{i\in\mathcal N}\bigl[p_i-c_iq_i^2-t_i(a_i-b_iq_i)-r\bigr]\cdot\exp(\alpha_iq_i-p_i+t_is_i).
--   $$
--   This rewriting removes the MNL denominator: it is the first step of the proof of Theorem 1, after which the profit can be maximized product by product for a fixed value of $r$.
--
--   **Formalization Note** Products are indexed by `Fin N` (0-based; the paper's product $i$ is index $i-1$); $N=0$ is allowed. Qualities range over all of $\mathbb R$, as in the proof of Theorem 1; the model's range $[0, a_i/b_i)$ (p. 8) is not imposed.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), p. 25, Appendix B, Proof of Theorem 1, eq. (15)

import Mathlib
import Definitions.Def_PriceQualityService_Joint_Model

namespace PriceQualityService.Joint

/-- (15), Wang, Ke & Cui, Appendix B, Proof of Theorem 1, p. 25: writing `r = Π(p, q, t; 𝒩)`,
`r = ∑_{i∈𝒩} [p_i − c_i q_i² − t_i(a_i − b_i q_i) − r] · exp(α_i q_i − p_i + t_i s_i)`. -/
theorem eq_15 {N : ℕ} (α a b c s p q t : Fin N → ℝ) :
    profit α a b c s p q t =
      ∑ i, (markup a b c p q t i - profit α a b c s p q t) *
        Real.exp (α i * q i - p i + t i * s i) := by sorry

end PriceQualityService.Joint
