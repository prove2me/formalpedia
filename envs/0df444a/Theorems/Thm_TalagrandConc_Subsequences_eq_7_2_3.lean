-- Prove2me | Theorems.Thm_TalagrandConc_Subsequences_eq_7_2_3
-- name    : TalagrandConc.Subsequences.eq_7_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:17.317742+00:00
-- url     : https://prove2.me/theorems/661c2ffd-700e-481c-8ad7-1b9b228d6c56
-- title:
--   Eq. (7.2.3) — a ≥ L(x) − 2√2 f_c(A(a),x)√L(x) for the longest common subsequence
-- statement:
--   Let $\Omega = [0,1]$ and $N, N' \ge 0$. For $x \in \Omega^{N+N'}$ let
--   $$L(x) = L_{N,N'}(x_1,\dots,x_N;\ x_{N+1},\dots,x_{N+N'})$$
--   be the length of the longest common subsequence of the first $N$ and the last $N'$ coordinates of $x$, and for $a > 0$ let $A(a) = \{x \;;\; L(x) \le a\}$. Then for every $x \in \Omega^{N+N'}$,
--   $$a \ge L(x) - 2\sqrt2\, f_c(A(a),x)\sqrt{L(x)},$$
--   where $f_c$ is Talagrand's convex hull distance on $\Omega^{N+N'}$.
--
--   This is the basic inequality of Section 7.2, the analogue of Lemma 7.1.1 for common subsequences; the factor $2\sqrt 2$ is what turns the constant $4$ of Theorem 7.1.2 into $32$ in Theorem 7.2.1.
--
--   **Formalization Note** Stated in the rearranged form $L(x) \le a + 2\sqrt2\, f_c(A(a),x)\sqrt{L(x)}$ in $[0,+\infty]$. The restriction $a > 0$ follows the definition of $A(a)$ in Section 7.1.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 155, Eq. (7.2.3)

import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic
import Definitions.Def_TalagrandConc_Subsequences_Basic

open MeasureTheory
open scoped ENNReal

namespace TalagrandConc.Subsequences

/-- Talagrand (1995), Eq. (7.2.3), p. 155. With `Ω = [0,1]`, `x ∈ Ω^{N+N'}`,
`L(x) = L_{N,N'}(x_1, …, x_N; x_{N+1}, …, x_{N+N'})` and `A(a) = {x ; L(x) ≤ a}`, for `a > 0`:
`a ≥ L(x) − 2√2 f_c(A(a), x) √(L(x))`, written as
`L(x) ≤ a + 2√2 f_c(A(a), x) √(L(x))` in `ℝ≥0∞`. -/
theorem eq_7_2_3 {N N' : ℕ} (a : ℝ) (ha : 0 < a) (x : Fin (N + N') → unitInterval) :
    ((lcsJoint x : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal a + ENNReal.ofReal (2 * Real.sqrt 2) * TalagrandConc.ConvexHull.fc (levelSet lcsJoint a) x *
        ENNReal.ofReal (Real.sqrt (lcsJoint x)) := by sorry

end TalagrandConc.Subsequences
