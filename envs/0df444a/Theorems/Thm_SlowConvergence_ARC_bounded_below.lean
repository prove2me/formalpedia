-- Prove2me | Theorems.Thm_SlowConvergence_ARC_bounded_below
-- name    : SlowConvergence.ARC.bounded_below
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:44:38.64595+00:00
-- url     : https://prove2.me/theorems/b9881998-04ff-4d0a-8b16-8522795eedf7
-- title:
--   §5, p. 15 — $f_4$ is bounded below by zero: the values $f_{4,k}$ of (5.3) and every segment piece are nonnegative
-- statement:
--   Let $0<\tau<1$ and $\eta = \tfrac12\big(\tfrac2{3-2\tau}-\tfrac23\big)$. The values defined by (5.3),
--   $$f_{4,0} = \tfrac23\,\zeta(1+3\eta),\qquad f_{4,k+1} = f_{4,k} - \tfrac23\Big(\frac1{k+1}\Big)^{1+3\eta},$$
--   satisfy $f_{4,k}\ge0$ for every $k\ge0$. Moreover, with $s_k = (1/(k+1))^{1/3+\eta}$ and $p_k$ the quintic Hermite piece of (2.11) with coefficients $c_{0,k}=\tfrac23(1/(k+1))^{1+3\eta}$, $c_{1,k}=-(1/(k+1))^{2/3+2\eta}$, $c_{2,k}=0$ and (5.11), the function
--   $$f_4(x) = p_k(x-x_k) + f_{4,k+1}\qquad (x\in[x_k,x_{k+1}])$$
--   of p. 14 is nonnegative on every segment:
--   $$p_k(t) + f_{4,k+1} \ge 0 \qquad\text{for all } t\in[0,s_k].$$
--
--   This is the paper's claim that $f_4$ is bounded below by zero on $[0,\infty)$: the decrements of (5.3) sum to $f_{4,0}$, because $1+3\eta>1$ makes the zeta series converge.
--
--   **Formalization Note** $f_4$ itself is not defined as a glued function; its value on $[x_k,x_{k+1}]$ is written out as $p_k(x-x_k)+f_4(x_{k+1})$ with $f_4(x_{k+1}) = f_{4,k+1}$, as (3.1) requires. Boundedness below of the extended function on all of $\mathbb R$ is part of the goal theorem.
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 13, (5.3); p. 15, §5

import Mathlib
import Definitions.Def_SlowConvergence_ARC_Data
import Definitions.Def_SlowConvergence_ARC_Pieces

namespace SlowConvergence.ARC

/-- Cartis, Gould & Toint, preprint 15 Oct 2009, §5, p. 15: "The fact that f(x) is bounded below by zero
finally results from (5.3) and the definition of the Riemann ζ function." For `0 < τ < 1` and every
`k ≥ 0`: the prescribed function values (5.3), `f_{4,0} = ⅔ζ(1 + 3η)` and
`f_{4,k+1} = f_{4,k} − ⅔(1/(k+1))^{1+3η}`, satisfy `f_{4,k} ≥ 0`; and on the segment `[x_k, x_{k+1}]`
the function `f_4(x) = p_k(x − x_k) + f_4(x_{k+1})` of p. 14 (with `f_4(x_{k+1}) = f_{4,k+1}`) is
nonnegative: `p_k(t) + f_{4,k+1} ≥ 0` for every `t ∈ [0, s_k]`. -/
theorem bounded_below (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (k : ℕ) :
    0 ≤ fk τ k ∧ ∀ t ∈ Set.Icc 0 (sk τ k), 0 ≤ p τ k t + fk τ (k + 1) := by sorry

end SlowConvergence.ARC
