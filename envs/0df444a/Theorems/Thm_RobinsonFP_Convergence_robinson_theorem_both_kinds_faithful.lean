-- Prove2me | Theorems.Thm_RobinsonFP_Convergence_robinson_theorem_both_kinds_faithful
-- name    : RobinsonFP.Convergence.robinson_theorem_both_kinds_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:03:31.528986+00:00
-- url     : https://prove2.me/theorems/4b4ad8fc-4a28-436a-8a27-c7cc814bb016
-- title:
--   Robinson's Theorem (1951) for vector systems of either kind (Definition 1 or the alternate notion)
-- statement:
--   Let $A=(a_{ij})$ be a real $m\times n$ matrix with $m,n\ge 1$, the pay-off matrix of a finite two-person zero-sum game, and let $v$ be its value, given by a solution $(X,Y)$. Let $(U,V)$ consist of $n$-dimensional vectors $U(0),U(1),\dots$ and $m$-dimensional vectors $V(0),V(1),\dots$ with $\min U(0)=\max V(0)$ and, for every $t$,
--   $$U(t+1)=U(t)+A_{i\cdot},\qquad V(t+1)=V(t)+A_{\cdot j},$$
--   where $v_i(t)=\max V(t)$ and either
--   1. $u_j(t)=\min U(t)$ (a vector system in the sense of Definition 1), or
--   2. $u_j(t+1)=\min U(t+1)$ (the alternate notion of vector system).
--
--   Then
--   $$\lim_{t\to\infty}\frac{\min U(t)}{t}=\lim_{t\to\infty}\frac{\max V(t)}{t}=v.$$
--
--   This is the Theorem of Robinson (1951, p. 297) in the scope the paper asserts it: the paper states that "in all the following proofs and theorems, either definition may be used". The existing theorem `RobinsonFP.Convergence.robinson_theorem` covers case 1 only; this statement adds the alternate (alternating-update) form of fictitious play.
--
--   **Formalization Note** Ties in the choice of $i$ and $j$ may be broken arbitrarily at each step. At $t=0$ the quotient is Lean's $x/0=0$, which does not affect the limits.
-- source:
--   Robinson, An Iterative Method of Solving a Game, Ann. of Math. 54(2) (1951), pp. 296–301, doi:10.2307/1969530, p. 297, Theorem (with the alternate notion of vector system, p. 297)

import Mathlib
import Definitions.Def_RobinsonFP_Convergence_VectorSystem

open Filter Topology

namespace RobinsonFP.Convergence

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem robinson_theorem_both_kinds_faithful [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ)
    (hUV : IsVectorSystem A U V ∨ IsAltVectorSystem A U V)
    (x : ι → ℝ) (y : κ → ℝ) (v : ℝ) (hsol : IsSolution A x y v) :
    Tendsto (fun t : ℕ => vmin (U t) / t) atTop (𝓝 v) ∧
      Tendsto (fun t : ℕ => vmax (V t) / t) atTop (𝓝 v) := by sorry

end RobinsonFP.Convergence
