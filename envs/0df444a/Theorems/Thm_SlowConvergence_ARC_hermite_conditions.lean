-- Prove2me | Theorems.Thm_SlowConvergence_ARC_hermite_conditions
-- name    : SlowConvergence.ARC.hermite_conditions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:38.887013+00:00
-- url     : https://prove2.me/theorems/4fc2551b-8da8-4f2f-b8c5-19b02568a6fc
-- title:
--   §5, (5.9)–(5.11), p. 14 — the coefficients (5.11) solve the Hermite interpolation conditions on $[0,s_k]$
-- statement:
--   Let $0<\tau<1$ and let $p_k$ be the quintic of the form (2.11) with $c_{0,k} = \tfrac23(1/(k+1))^{1+3\eta}$, $c_{1,k} = -(1/(k+1))^{\frac23+2\eta}$, $c_{2,k}=0$ and $c_{3,k}, c_{4,k}, c_{5,k}$ given by (5.11). Then for every $k\ge0$, with $s_k = (1/(k+1))^{\frac13+\eta}$,
--   $$p_k(0) = \tfrac23\Big(\frac1{k+1}\Big)^{1+3\eta},\qquad p_k(s_k) = 0, \tag{5.9}$$
--   $$p_k'(0) = -\Big(\frac1{k+1}\Big)^{\frac23+2\eta},\qquad p_k'(s_k) = -\Big(\frac1{k+2}\Big)^{\frac23+2\eta},\qquad p_k''(0) = p_k''(s_k) = 0. \tag{5.10}$$
--
--   These conditions make the glued function $f_4$ twice continuously differentiable across the iterates, with the prescribed values, gradients and zero Hessians there.
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 14, §5, (5.9)–(5.11); form (2.11), p. 4

import Mathlib
import Definitions.Def_SlowConvergence_ARC_Data
import Definitions.Def_SlowConvergence_ARC_Pieces

namespace SlowConvergence.ARC

/-- Cartis, Gould & Toint, preprint 15 Oct 2009, §5, (5.9)–(5.11), p. 14: the quintic `p_k` of the form
(2.11) with coefficients `c_{0,k} = ⅔(1/(k+1))^{1+3η}`, `c_{1,k} = −(1/(k+1))^{2/3+2η}`, `c_{2,k} = 0` and
(5.11) satisfies the interpolation conditions on `[0, s_k]`: for `0 < τ < 1` and every `k ≥ 0`,
(5.9) `p_k(0) = ⅔(1/(k+1))^{1+3η}`, `p_k(s_k) = 0`, and
(5.10) `p_k'(0) = −(1/(k+1))^{2/3+2η}`, `p_k'(s_k) = −(1/(k+2))^{2/3+2η}`, `p_k''(0) = p_k''(s_k) = 0`. -/
theorem hermite_conditions (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (k : ℕ) :
    p τ k 0 = 2 / 3 * (1 / ((k : ℝ) + 1)) ^ (1 + 3 * eta τ) ∧
      p τ k (sk τ k) = 0 ∧
      deriv (p τ k) 0 = -(1 / ((k : ℝ) + 1)) ^ (2 / 3 + 2 * eta τ) ∧
      deriv (p τ k) (sk τ k) = -(1 / ((k : ℝ) + 2)) ^ (2 / 3 + 2 * eta τ) ∧
      iteratedDeriv 2 (p τ k) 0 = 0 ∧
      iteratedDeriv 2 (p τ k) (sk τ k) = 0 := by sorry

end SlowConvergence.ARC
