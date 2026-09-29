-- Prove2me | Theorems.Thm_Roberts1997_RWM_min_one_exp_lipschitz
-- name    : Roberts1997.RWM.min_one_exp_lipschitz
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:46:52.017583+00:00
-- url     : https://prove2.me/theorems/17e7bcfa-d08e-4868-a3d4-cdabbffc181b
-- title:
--   Proposition 2.2 — g(x) = 1 ∧ eˣ is Lipschitz with coefficient 1
-- statement:
--   Let $g(x)=1\wedge e^x=\min(1,e^x)$. Then $g$ is Lipschitz with coefficient 1:
--
--   $$ |g(x)-g(y)|\le|x-y|\qquad\text{for all }x,y\in\mathbb R. $$
--
--   The acceptance probability of the Metropolis algorithm is $g$ of the log target ratio, so this inequality converts approximations of the log ratio into approximations of the acceptance probability; it is used in the proof of Lemma 2.6.
-- source:
--   Roberts, Gelman, Gilks, Weak convergence and optimal scaling of random walk Metropolis algorithms, Ann. Appl. Probab. 7(1), 1997, p. 115, Proposition 2.2

import Mathlib

namespace Roberts1997.RWM

/-- Proposition 2.2 (p. 115). `g(x) = 1 ∧ e^x` is Lipschitz with coefficient 1:
`|g(x) - g(y)| ≤ |x - y|` for all `x, y ∈ ℝ`. -/
theorem min_one_exp_lipschitz (x y : ℝ) :
    |min 1 (Real.exp x) - min 1 (Real.exp y)| ≤ |x - y| := by sorry

end Roberts1997.RWM
