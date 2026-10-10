-- Prove2me | Theorems.Thm_PriceQualityService_Joint_eq_17
-- name    : PriceQualityService.Joint.eq_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:22:34.34993+00:00
-- url     : https://prove2.me/theorems/607d816f-86db-4fa4-b949-af41c637274f
-- title:
--   (17): for fixed $\mathbf q,\mathbf t$ the optimal profit over prices is the unique root of $r=\sum_i e^{\alpha_iq_i-c_iq_i^2+t_i(s_i-(a_i-b_iq_i))-r-1}$
-- statement:
--   Fix quality levels $\mathbf q$ and service durations $\mathbf t$. The equation
--   $$
--   r=\sum_{i\in\mathcal N}\exp\bigl(\alpha_iq_i-c_iq_i^2+t_i(s_i-(a_i-b_iq_i))-r-1\bigr)
--   $$
--   has exactly one real solution $r$. This $r$ is the largest profit the firm can earn by choosing prices: $\Pi(\mathbf p,\mathbf q,\mathbf t;\mathcal N)\le r$ for every price vector $\mathbf p$, with equality at
--   $$
--   p_i=1+r+c_iq_i^2+t_i(a_i-b_iq_i)\qquad(i\in\mathcal N).
--   $$
--   This is the price-only optimization of the MNL model with fixed quality and service: every product carries the same markup $1+r$, and the optimal profit is characterized by a one-dimensional equation.
--
--   **Formalization Note** Products are indexed by `Fin N` (0-based; the paper's product $i$ is index $i-1$); $N=0$ is allowed. Qualities range over all of $\mathbb R$, as in the proof of Theorem 1; the model's range $[0, a_i/b_i)$ (p. 8) is not imposed.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), p. 26, Appendix B, Proof of Theorem 1, eq. (17)

import Mathlib
import Definitions.Def_PriceQualityService_Joint_Model

namespace PriceQualityService.Joint

/-- (17), Appendix B, Proof of Theorem 1, p. 26: for fixed qualities `q` and durations `t`, the
equation `r = ∑_i exp(α_i q_i − c_i q_i² + t_i(s_i − (a_i − b_i q_i)) − r − 1)` has exactly one real
root `r`; it is the maximal profit over all price vectors, attained at
`p_i = 1 + r + c_i q_i² + t_i(a_i − b_i q_i)`. -/
theorem eq_17 {N : ℕ} (α a b c s q t : Fin N → ℝ) :
    ∃ r : ℝ,
      r = ∑ i, Real.exp (α i * q i - c i * q i ^ 2 + t i * (s i - (a i - b i * q i)) - r - 1) ∧
      (∀ r' : ℝ,
        r' = ∑ i, Real.exp (α i * q i - c i * q i ^ 2 + t i * (s i - (a i - b i * q i)) - r' - 1) →
          r' = r) ∧
      (∀ p : Fin N → ℝ, profit α a b c s p q t ≤ r) ∧
      profit α a b c s (fun i => 1 + r + c i * q i ^ 2 + t i * (a i - b i * q i)) q t = r := by sorry

end PriceQualityService.Joint
