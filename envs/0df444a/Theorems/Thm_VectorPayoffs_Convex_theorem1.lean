-- Prove2me | Theorems.Thm_VectorPayoffs_Convex_theorem1
-- name    : VectorPayoffs.Convex.theorem1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:08:34.826837+00:00
-- url     : https://prove2.me/theorems/ef899460-4503-4d22-857c-1671543ba194
-- title:
--   THEOREM 1 — Blackwell's sufficient condition for approachability
-- statement:
--   Let $S\subseteq\mathbb R^N$ be closed. Suppose that for every $x\notin S$ there is $p(x)\in P$ such that, for a point $y\in S$ closest to $x$, the hyperplane through $y$ perpendicular to the segment $xy$ separates $x$ from $R(p(x))$:
--   $$\langle x-y,\;w-y\rangle\le 0\qquad\text{for all }w\in R(p(x)).$$
--   Then $S$ is approachable with every strategy $f$ of I satisfying
--   $$f_n(x_1,\dots,x_n)=p(\bar x_n)\quad\text{whenever }n>0\text{ and }\bar x_n=\tfrac1n\textstyle\sum_{i=1}^n x_i\notin S,$$
--   $f_n$ being arbitrary if $n=0$ or $\bar x_n\in S$.
--
--   This is the paper's sufficient condition for approachability; together with the minimax theorem it yields the characterization of approachable convex sets (THEOREM 3).
--
--   **Formalization Note** "The closest point" is read as *some* closest point $y$ (for non-convex $S$ it need not be unique) and "separates" as weak separation (closed half-space). The map $p$ is not assumed measurable; the conclusion is about every (measurable) strategy $f$ that agrees with $p(\bar x_n)$ off $S$.
-- source:
--   Blackwell, An analog of the minimax theorem for vector payoffs, Pacific J. Math. 6(1), 1956, p. 3, THEOREM 1

import Mathlib
import Definitions.Def_VectorPayoffs_Convex_Game

open MeasureTheory

namespace VectorPayoffs.Convex

/-- Blackwell (1956), §2, p. 3, THEOREM 1: if every `x ∉ S` admits `p(x) ∈ P` such that the
hyperplane through a closest point `y ∈ S` perpendicular to `xy` separates `x` from `R(p(x))`,
then `S` is approachable with any strategy playing `p(x̄ₙ)` whenever `n > 0` and `x̄ₙ ∉ S`. -/
theorem theorem1 {N r s : ℕ} (G : Game N r s) (S : Set (E N)) (hS : IsClosed S)
    (p : E N → Fin r → ℝ)
    (hsep : ∀ x ∉ S, p x ∈ stdSimplex ℝ (Fin r) ∧ G.BlackwellCondition S (p x) x)
    (f : Strategy N r)
    (hf : ∀ n, 1 ≤ n → ∀ h : Fin n → E N, avgHist h ∉ S → f.toFun n h = p (avgHist h)) :
    G.ApproachableWith S f := by sorry

end VectorPayoffs.Convex
