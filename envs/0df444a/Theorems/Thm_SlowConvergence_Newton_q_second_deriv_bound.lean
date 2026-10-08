-- Prove2me | Theorems.Thm_SlowConvergence_Newton_q_second_deriv_bound
-- name    : SlowConvergence.Newton.q_second_deriv_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:39:49.728003+00:00
-- url     : https://prove2.me/theorems/e87551b5-1ca8-46ae-9823-87f59576d382
-- title:
--   §3, p. 8 — $|q_k''(t)| \le 219$ for all $k \ge 0$ and $t \in [0,1]$
-- statement:
--   Let $q_k$ be the quintic of §3, pp. 7–8, with the printed coefficients $d_{0,k}, \dots, d_{5,k}$. Then for every $k \ge 0$ and every $t \in [0,1]$
--   $$|q_k''(t)| \le 219 .$$
--
--   This is the uniform bound on the second derivative of the second-coordinate function $f_{2,2}$; together with the bound on $p_k''$ it shows that the Hessian of $f_2$ is uniformly bounded.
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 8, §3

import Mathlib
import Definitions.Def_SlowConvergence_Newton_Data
import Definitions.Def_SlowConvergence_Newton_Pieces

open scoped RealInnerProductSpace

namespace SlowConvergence.Newton

/-- Cartis, Gould & Toint, preprint 15 Oct 2009, §3, p. 8: `|q_k''(t)| ≤ 219` for all `k ≥ 0` and all
`t ∈ [0, 1]`. -/
theorem q_second_deriv_bound (k : ℕ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (q k)) t| ≤ 219 := by sorry

end SlowConvergence.Newton
