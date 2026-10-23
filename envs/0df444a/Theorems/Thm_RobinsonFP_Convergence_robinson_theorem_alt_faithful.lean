-- Prove2me | Theorems.Thm_RobinsonFP_Convergence_robinson_theorem_alt_faithful
-- name    : RobinsonFP.Convergence.robinson_theorem_alt_faithful
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-23T01:03:35.253587+00:00
-- url     : https://prove2.me/theorems/a145e0d4-0326-4255-8363-3f3a4a716de4
-- title:
--   Robinson's Theorem (1951) for the alternate notion of vector system
-- statement:
--   Let $A=(a_{ij})$ be a real $m\times n$ matrix with $m,n\ge 1$ and value $v$, given by a solution $(X,Y)$. Let $(U,V)$ be a vector system of the alternate kind: $\min U(0)=\max V(0)$ and, for every $t$,
--   $$U(t+1)=U(t)+A_{i\cdot},\qquad V(t+1)=V(t)+A_{\cdot j},\qquad v_i(t)=\max V(t),\quad u_j(t+1)=\min U(t+1).$$
--   Then
--   $$\lim_{t\to\infty}\frac{\min U(t)}{t}=\lim_{t\to\infty}\frac{\max V(t)}{t}=v.$$
--
--   This is Robinson's Theorem (1951, p. 297) for the alternate (alternating-update) notion of vector system, which the paper covers by the remark that either definition may be used in all its proofs and theorems. The existing theorem `RobinsonFP.Convergence.robinson_theorem` proves the case of Definition 1.
--
--   **Formalization Note** Ties are broken arbitrarily at each step; at $t=0$ the quotient is Lean's $x/0=0$, irrelevant for the limits.
-- source:
--   Robinson, An Iterative Method of Solving a Game, Ann. of Math. 54(2) (1951), doi:10.2307/1969530, p. 297, Theorem with the alternate notion of vector system

import Mathlib
import Definitions.Def_RobinsonFP_Convergence_VectorSystem

open Filter Topology

namespace RobinsonFP.Convergence

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem robinson_theorem_alt_faithful [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsAltVectorSystem A U V)
    (x : ι → ℝ) (y : κ → ℝ) (v : ℝ) (hsol : IsSolution A x y v) :
    Tendsto (fun t : ℕ => vmin (U t) / t) atTop (𝓝 v) ∧
      Tendsto (fun t : ℕ => vmax (V t) / t) atTop (𝓝 v) := by sorry

end RobinsonFP.Convergence
