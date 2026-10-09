-- Prove2me | Theorems.Thm_ProjReflGrad_Linear_eq_yn_z
-- name    : ProjReflGrad.Linear.eq_yn_z
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:15:52.175985+00:00
-- url     : https://prove2.me/theorems/77175842-b045-416e-a2fe-a42ec23ce319
-- title:
--   Proof of Theorem 3.3, p. 6 — ‖y_n − z‖² = 2‖x_n − z‖² − ‖x_{n−1} − z‖² + 2‖x_n − x_{n−1}‖² (Lemma 2.5)
-- statement:
--   Let $(x_n),(y_n)$ be a run of Algorithm 3.1 in a real inner product space $H$ (so $y_n=2x_n-x_{n-1}$ for $n\ge1$), and let $z\in H$ be any point. Then for every $n\ge1$
--   $$\|y_n-z\|^2=2\|x_n-z\|^2-\|x_{n-1}-z\|^2+2\|x_n-x_{n-1}\|^2\ \ge\ 2\|x_n-z\|^2-\|x_{n-1}-z\|^2 .$$
--
--   This is Lemma 2.5 ($\|2u-v\|^2=2\|u\|^2-\|v\|^2+2\|u-v\|^2$) applied with $u=x_n-z$, $v=x_{n-1}-z$. It is the bound on $\|y_n-z\|^2$ through which strong monotonicity at the reflected point $y_n$ is turned into a statement about the iterates $x_n$, $x_{n-1}$.
--
--   **Formalization Note.** Only the reflection step of the run is used; $z$ is arbitrary and no hypotheses on $C$, $F$ or $\lambda$ are needed. The range is $n\ge1$ because $y_n=2x_n-x_{n-1}$ holds from $n=1$ on.
-- source:
--   Malitsky, Projected Reflected Gradient Methods for Monotone Variational Inequalities, arXiv:1502.04968v1, p. 6, proof of Theorem 3.3 (display after 'Note that by Lemma 2.5'); Lemma 2.5, p. 3

import Mathlib
import Definitions.Def_ProjReflGrad_Linear_Setting

namespace ProjReflGrad.Linear

/-- Proof of Theorem 3.3 (Malitsky 2015, p. 6), via Lemma 2.5: along a run of Algorithm 3.1, for
every `z` and `n ≥ 1`,
`‖y_n - z‖² = 2‖x_n - z‖² - ‖x_{n-1} - z‖² + 2‖x_n - x_{n-1}‖² ≥ 2‖x_n - z‖² - ‖x_{n-1} - z‖²`. -/
theorem eq_yn_z {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (F : H → H) (lam : ℝ) (x y : ℕ → H) (hrun : ProjReflGrad.Weak.IsPRGRun C F lam x y) (z : H) :
    ∀ n : ℕ, 1 ≤ n →
      ‖y n - z‖ ^ 2 = 2 * ‖x n - z‖ ^ 2 - ‖x (n - 1) - z‖ ^ 2 + 2 * ‖x n - x (n - 1)‖ ^ 2 ∧
      2 * ‖x n - z‖ ^ 2 - ‖x (n - 1) - z‖ ^ 2 ≤ ‖y n - z‖ ^ 2 := by sorry

end ProjReflGrad.Linear
