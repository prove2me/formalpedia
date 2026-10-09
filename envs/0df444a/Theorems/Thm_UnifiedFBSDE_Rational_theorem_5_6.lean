-- Prove2me | Theorems.Thm_UnifiedFBSDE_Rational_theorem_5_6
-- name    : UnifiedFBSDE.Rational.theorem_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:15:04.682025+00:00
-- url     : https://prove2.me/theorems/96af47fa-c10c-434c-9985-b723b67b5169
-- title:
--   Theorem 5.6, pp. 22–23 (corrected) — with σ₃ ≠ 0, hσ₃ ≠ 1, (5.3) has a solution satisfying (5.9) for arbitrary T iff one of four cases holds
-- statement:
--   Consider the linear FBSDE (4.1) with constant coefficients $b_i,\sigma_i,f_i$ ($i=1,2,3$) and terminal slope $h$, and let $F$ be the function (3.9),
--   $$
--   F(y)=f_1+f_2y+y(b_1+b_2y)+\frac{(f_3+b_3y)\,y\,(\sigma_1+\sigma_2y)}{1-\sigma_3y}.
--   $$
--   Assume $\sigma_3\neq0$ and $h\sigma_3\neq1$, and write $\alpha_3=b_2-b_3\sigma_2/\sigma_3$. Then the backward ODE (5.3),
--   $$
--   y_t=h+\int_t^TF(y_s)\,ds,\qquad t\in[0,T],
--   $$
--   has, for every $T>0$, a solution such that both $y$ and $(1-\sigma_3y)^{-1}$ are bounded on $[0,T]$ (condition (5.9)) if and only if one of the following holds:
--
--   1. $h<1/\sigma_3$, $F(h)\le0$, and either $F$ has a zero point in $(-\infty,h]$ or $\alpha_3=0$;
--   2. $h>1/\sigma_3$, $F(h)\ge0$, and either $F$ has a zero point in $[h,\infty)$ or $\alpha_3=0$;
--   3. $h<1/\sigma_3$, $F(h)\ge0$, and either $F$ has a zero point in $[h,1/\sigma_3)$ or $F(y)\to0$ as $y\uparrow1/\sigma_3$;
--   4. $h>1/\sigma_3$, $F(h)\le0$, and either $F$ has a zero point in $(1/\sigma_3,h]$ or $F(y)\to0$ as $y\downarrow1/\sigma_3$.
--
--   This is the sharp global-solvability criterion for the dominating ODE in the case $\sigma_3\neq0$; in the paper it is the criterion behind well-posedness of the linear FBSDE on every horizon.
--
--   **Formalization Note** The alternatives "$F(y)\to0$ as $y$ tends to $1/\sigma_3$ from the side of $h$" in cases 3 and 4 are a correction: they are not on the page, and without them the equivalence is false. For $\sigma_3=1$, $f_1=1$, $f_2=-1$, all other coefficients $0$ and $h=0$, $F(y)=1-y$, the solution $y_t=1-e^{t-T}$ satisfies (5.9) on every horizon, yet none of the printed cases holds (companion item `theorem_5_6_as_printed_fails`). The gap is in the Appendix, which claims $F$ is positive on the closed interval $[h,\sigma_3^{-1}]$ when $\alpha_0=0$. The limit is taken along one side only, so Lean's junk value of $F$ at the pole plays no role; every zero point in the cases lies off the pole.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, pp. 22–23, Theorem 5.6 (sufficiency: proof on p. 23; necessity: Appendix, pp. 47–48)

import Mathlib
import Definitions.Def_UnifiedFBSDE_Rational_Setting

open Filter Topology

namespace UnifiedFBSDE.Rational

/-- Theorem 5.6, pp. 22–23, **corrected**. Constant coefficients, `σ₃ ≠ 0`, `hσ₃ ≠ 1`. The ODE
(5.3) has a solution satisfying (5.9) for arbitrary `T` iff one of four cases holds. As printed,
cases (iii) and (iv) miss the possibility that `F(y) → 0` as `y` tends to the pole `1/σ₃` from
the side of `h` (then the solution approaches the pole only asymptotically); with
`σ₃ = 1, f₁ = 1, f₂ = −1`, other coefficients `0`, `h = 0` (so `F(y) = 1 − y`) the printed
equivalence fails. The extra disjuncts restore it. -/
theorem theorem_5_6 (c : Coeffs) (h : ℝ) (hσ : c.σ₃ ≠ 0) (hh : h * c.σ₃ ≠ 1) :
    (∀ T : ℝ, 0 < T → ∃ y : ℝ → ℝ, IsSolution59 c h T y) ↔
      -- (i)
      (h < 1 / c.σ₃ ∧ c.F h ≤ 0 ∧ ((∃ l : ℝ, l ≤ h ∧ c.F l = 0) ∨ c.α₃ = 0)) ∨
      -- (ii)
      (1 / c.σ₃ < h ∧ 0 ≤ c.F h ∧ ((∃ l : ℝ, h ≤ l ∧ c.F l = 0) ∨ c.α₃ = 0)) ∨
      -- (iii), with the corrective disjunct `F(y) → 0` as `y ↑ 1/σ₃`
      (h < 1 / c.σ₃ ∧ 0 ≤ c.F h ∧
        ((∃ l : ℝ, h ≤ l ∧ l < 1 / c.σ₃ ∧ c.F l = 0) ∨
          Tendsto c.F (𝓝[<] (1 / c.σ₃)) (𝓝 0))) ∨
      -- (iv), with the corrective disjunct `F(y) → 0` as `y ↓ 1/σ₃`
      (1 / c.σ₃ < h ∧ c.F h ≤ 0 ∧
        ((∃ l : ℝ, 1 / c.σ₃ < l ∧ l ≤ h ∧ c.F l = 0) ∨
          Tendsto c.F (𝓝[>] (1 / c.σ₃)) (𝓝 0))) := by sorry

end UnifiedFBSDE.Rational
