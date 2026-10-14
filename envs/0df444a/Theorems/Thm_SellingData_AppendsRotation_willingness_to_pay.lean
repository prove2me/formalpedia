-- Prove2me | Theorems.Thm_SellingData_AppendsRotation_willingness_to_pay
-- name    : SellingData.AppendsRotation.willingness_to_pay
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:42.019922+00:00
-- url     : https://prove2.me/theorems/60c33863-416c-425f-a76b-116d86cae3db
-- title:
--   §4.2, p. 20 — for c ≤ û, U_ij − U_i0 = −T_j + ∫_{v̲}^{c_i}(c_i − v) dH(v, α_j), increasing in c_i
-- statement:
--   In the data-append model, let $\alpha\in(0,1)$ and let $c$ be a targeting cost with $\underline v\le c\le\hat u$, so that the outside option is $\max\{\hat u-c,0\}=\hat u-c$. For every fee $T$, the marketer's incremental value from the plan $(T,\alpha)$ over its outside option is
--   $$
--   \Big(-T+\int_{c}^{\bar v}(v-c)\,dH(v,\alpha)\Big)-\max\{\hat u-c,0\}=-T+\int_{\underline v}^{c}(c-v)\,dH(v,\alpha),
--   $$
--   and this quantity is strictly increasing in $c$ on $[\underline v,\hat u]$.
--
--   This is why, when $c_L<c_H<\hat u$, the high-cost marketers value any given plan more than the low-cost ones and become the "high type" of the screening problem: the binding constraints switch from those of marketing lists to $IR_L$ and $IC_{H,L}$.
--
--   **Formalization Note.** The page writes $U_{ij}-U_{i0}=\int_{\underline v}^{c_i}(c_i-v)\,dH(v,\alpha_j)$ without the fee; the proof of Proposition 8 (p. 33) has $-T_j+$, and the fee is included here. The identity uses that $\hat u$ is the mean of every $H(\cdot,\alpha)$.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), p. 20, §4.2

import Mathlib
import Definitions.Def_SellingData_AppendsRotation_Setting

namespace SellingData.AppendsRotation

open Set

/-- §4.2, p. 20: for a cost `c` between `v̲` and `û`, a marketer's incremental value from the plan
`(T, α)` over the outside option `max{û − c, 0}` is `−T + ∫_{v̲}^{c} (c − v) dH(v, α)`, and it is
strictly increasing in `c`. -/
theorem willingness_to_pay (M : Model) :
    (∀ α ∈ Ioo (0 : ℝ) 1, ∀ c ∈ Icc M.vLo M.uHat, ∀ T : ℝ,
      M.U c T α - M.outside c = -T + ∫ v in M.vLo..c, (c - v) * M.h v α) ∧
    (∀ α ∈ Ioo (0 : ℝ) 1, ∀ T : ℝ,
      StrictMonoOn (fun c => M.U c T α - M.outside c) (Icc M.vLo M.uHat)) := by sorry

end SellingData.AppendsRotation
