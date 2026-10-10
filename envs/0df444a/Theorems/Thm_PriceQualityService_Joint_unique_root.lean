-- Prove2me | Theorems.Thm_PriceQualityService_Joint_unique_root
-- name    : PriceQualityService.Joint.unique_root
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:22:46.038972+00:00
-- url     : https://prove2.me/theorems/1d8502ba-58f7-4f11-8207-5bc061cf4521
-- title:
--   $H(r)=\sum_i e^{k_i-r-1}$ is decreasing and $r=H(r)$ has a unique root
-- statement:
--   Let $(k_i)_{i\in\mathcal N}$ be real numbers and
--   $$
--   H(r)=\sum_{i\in\mathcal N}\exp(k_i-r-1).
--   $$
--   Then $H$ is non-increasing in $r$, strictly decreasing when $\mathcal N$ is nonempty, and the equation
--   $$
--   r=H(r)
--   $$
--   has exactly one real solution $r^*$. Applied with $k_i=\frac{b_i^2t_i^{*2}}{4c_i}+\bigl(s_i-a_i+\frac{\alpha_ib_i}{2c_i}\bigr)t_i^*+\frac{\alpha_i^2}{4c_i}$, this is the existence and uniqueness of the number $r^*$ in Theorem 1(c).
--
--   **Formalization Note** When $N=0$, $H\equiv0$ is not strictly decreasing and the unique root is $r^*=0$; the strict monotonicity is therefore stated under $N>0$, while the unique-root claim holds for all $N$.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), p. 27, Appendix B, Proof of Theorem 1, last paragraph

import Mathlib
import Definitions.Def_PriceQualityService_Joint_Model

namespace PriceQualityService.Joint

/-- Appendix B, Proof of Theorem 1, p. 27: for reals `k_i`, the map
`H(r) = ∑_{i∈𝒩} exp(k_i − r − 1)` is decreasing in `r`, strictly when `𝒩` is nonempty, and the
equation `r = H(r)` has exactly one real solution `r*`. -/
theorem unique_root {N : ℕ} (k : Fin N → ℝ) :
    Antitone (fun r : ℝ => ∑ i, Real.exp (k i - r - 1)) ∧
      (0 < N → StrictAnti (fun r : ℝ => ∑ i, Real.exp (k i - r - 1))) ∧
      ∃! r : ℝ, r = ∑ i, Real.exp (k i - r - 1) := by sorry

end PriceQualityService.Joint
