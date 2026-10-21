-- Prove2me | Theorems.Thm_ProxBundle_GPB_eq_7
-- name    : ProxBundle.GPB.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:29:35.863653+00:00
-- url     : https://prove2.me/theorems/9e2ffb89-9e3e-4abb-9ac2-d3faf836bbe3
-- title:
--   Equation (7), p. 5 — hybrid descent inequality
-- statement:
--   Let $f'$ be a subgradient oracle of the convex function $f$ on $D=\operatorname{dom}h$. Suppose its values satisfy $\|f'(x)-f'(y)\|\le2M+L\|x-y\|$ for nonnegative $M,L$ and all $x,y\in D$. With $\ell_f(x;y)=f(y)+\langle f'(y),x-y\rangle$, the bound is
--   $$
--   f(x)-\ell_f(x;y)\le2M\|x-y\|+\frac L2\|x-y\|^2\qquad(x,y\in D).
--   $$
--   The factor $L/2$ is used in the null-iteration and proximal estimates.
--
--   **Formalization Note** The oracle and function values are represented only on $D$; the source's global lower semicontinuity of $f$ is omitted.
-- source:
--   Liang & Monteiro, arXiv:2110.01084v3, p. 5, §2.1, (7)

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model

namespace ProxBundle.GPB

/-- Equation (7), p. 5: the hybrid oracle gives the precise factor `L/2`. -/
theorem eq_7 {n : ℕ} (P : Instance n) (μ M L : ℝ)
    (hμ : 0 ≤ μ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hA1 : P.A1 μ) (hA3 : P.A3 M L) :
    ∀ x ∈ P.D, ∀ y ∈ P.D,
      P.f x - P.ellf x y ≤ 2 * M * ‖x - y‖ + L / 2 * ‖x - y‖ ^ 2 := by sorry

end ProxBundle.GPB
