-- Prove2me | Theorems.Thm_SlowConvergence_Newton_q_interpolation
-- name    : SlowConvergence.Newton.q_interpolation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:40:55.650804+00:00
-- url     : https://prove2.me/theorems/b0af2537-ec1d-4d34-8ff5-5cf7da3743e1
-- title:
--   §3, pp. 7–8 — $q_k$ with the printed coefficients meets its six interpolation conditions
-- statement:
--   For $k \ge 0$ let $q_k(t) = d_{0,k} + d_{1,k}t + d_{2,k}t^2 + d_{3,k}t^3 + d_{4,k}t^4 + d_{5,k}t^5$ with
--   $$d_{0,k} = \tfrac12\Big(\frac1{k+1}\Big)^2,\quad d_{1,k} = -\Big(\frac1{k+1}\Big)^2,\quad d_{2,k} = \tfrac12\Big(\frac1{k+1}\Big)^2,$$
--   $$\begin{pmatrix} d_{3,k}\\ d_{4,k}\\ d_{5,k}\end{pmatrix} = \frac12\begin{pmatrix} 9\big(\frac1{k+2}\big)^2 - \big(\frac1{k+1}\big)^2\\ -16\big(\frac1{k+2}\big)^2 + 2\big(\frac1{k+1}\big)^2\\ 7\big(\frac1{k+2}\big)^2 - \big(\frac1{k+1}\big)^2\end{pmatrix}.$$
--   Then
--   $$q_k(0) = \tfrac12\Big(\frac1{k+1}\Big)^2,\quad q_k(1) = 0,\quad q_k'(0) = -\Big(\frac1{k+1}\Big)^2,\quad q_k'(1) = -\Big(\frac1{k+2}\Big)^2,$$
--   $$q_k''(0) = \Big(\frac1{k+1}\Big)^2,\quad q_k''(1) = \Big(\frac1{k+2}\Big)^2 .$$
--
--   These conditions make the second-coordinate function $f_{2,2}$ (equal to $q_k$ on $[k, k+1]$, shifted by the next knot value) twice continuously differentiable on $[0,\infty)$ with the values (3.10), slopes $-(1/(k+1))^2$ and curvatures $(1/(k+1))^2$ at the knots required by (3.3)–(3.4).
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, pp. 7–8, §3

import Mathlib
import Definitions.Def_SlowConvergence_Newton_Data
import Definitions.Def_SlowConvergence_Newton_Pieces

open scoped RealInnerProductSpace

namespace SlowConvergence.Newton

/-- Cartis, Gould & Toint, preprint 15 Oct 2009, §3, pp. 7–8: the quintic `q_k` with coefficients
`d_{0,k} = ½(1/(k+1))²`, `d_{1,k} = −(1/(k+1))²`, `d_{2,k} = ½(1/(k+1))²` and
`(d_{3,k}, d_{4,k}, d_{5,k})` as printed on p. 8 satisfies the interpolation conditions on `[0, 1]`:
`q_k(0) = ½(1/(k+1))²`, `q_k(1) = 0`, `q_k'(0) = −(1/(k+1))²`, `q_k'(1) = −(1/(k+2))²`,
`q_k''(0) = (1/(k+1))²` and `q_k''(1) = (1/(k+2))²`, for every `k ≥ 0`. -/
theorem q_interpolation (k : ℕ) :
    q k 0 = 1 / 2 * (1 / ((k : ℝ) + 1)) ^ 2 ∧
      q k 1 = 0 ∧
      deriv (q k) 0 = -((1 / ((k : ℝ) + 1)) ^ 2) ∧
      deriv (q k) 1 = -((1 / ((k : ℝ) + 2)) ^ 2) ∧
      deriv (deriv (q k)) 0 = (1 / ((k : ℝ) + 1)) ^ 2 ∧
      deriv (deriv (q k)) 1 = (1 / ((k : ℝ) + 2)) ^ 2 := by sorry

end SlowConvergence.Newton
