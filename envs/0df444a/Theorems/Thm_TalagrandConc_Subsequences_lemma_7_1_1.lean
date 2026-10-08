-- Prove2me | Theorems.Thm_TalagrandConc_Subsequences_lemma_7_1_1
-- name    : TalagrandConc.Subsequences.lemma_7_1_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:19.485654+00:00
-- url     : https://prove2.me/theorems/f713b3b0-eb40-4df4-9ee3-0c3a64c2db86
-- title:
--   Lemma 7.1.1 — a ≥ L_N(x) − f_c(A(a),x)√L_N(x)
-- statement:
--   Let $\Omega = [0,1]$, $N \ge 0$, and for $x \in \Omega^N$ let $L_N(x)$ be the length of the longest increasing subsequence of $x_1,\dots,x_N$. For $a > 0$ let $A(a) = \{x \in \Omega^N \;;\; L_N(x) \le a\}$, and let $f_c$ be Talagrand's convex hull distance. Then for every $x \in \Omega^N$,
--   $$a \ge L_N(x) - f_c(A(a),x)\sqrt{L_N(x)}. \tag{7.1.1}$$
--   In particular, for every real $v$,
--   $$L_N(x) \ge a + v \;\Rightarrow\; f_c(A(a),x) \ge \frac{v}{\sqrt{a+v}}. \tag{7.1.2}$$
--
--   This deterministic inequality converts a large value of $L_N$ into a large convex hull distance to the level set $A(a)$; combined with Theorem 4.1.1 it yields the concentration of $L_N$ (Theorem 7.1.2).
--
--   **Formalization Note** Inequality (7.1.1) is stated in the rearranged form $L_N(x) \le a + f_c(A(a),x)\sqrt{L_N(x)}$ in $[0,+\infty]$, where $f_c(A(a),x) = +\infty$ if $A(a) = \emptyset$. The page leaves the range of $v$ implicit; the statement is made for every real $v$ (for $v < 0$, or $a + v \le 0$, the right-hand side is $\le 0$ and the implication is trivial; Lean's conventions $\sqrt{t} = 0$ for $t \le 0$ and $t/0 = 0$ give the same).
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 153, Lemma 7.1.1, Eqs. (7.1.1)–(7.1.2)

import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic
import Definitions.Def_TalagrandConc_Subsequences_Basic

open MeasureTheory
open scoped ENNReal

namespace TalagrandConc.Subsequences

/-- Talagrand (1995), Lemma 7.1.1, p. 153. For `a > 0` and every `x ∈ [0,1]^N`,
(7.1.1) `a ≥ L_N(x) − f_c(A(a), x) √(L_N(x))`, written as `L_N(x) ≤ a + f_c(A(a), x) √(L_N(x))`
in `ℝ≥0∞` (where `f_c = +∞` when `A(a) = ∅`), and
(7.1.2) `L_N(x) ≥ a + v ⇒ f_c(A(a), x) ≥ v / √(a + v)` for every real `v`
(for `v < 0` the bound is trivial). -/
theorem lemma_7_1_1 {N : ℕ} (a : ℝ) (ha : 0 < a) (x : Fin N → unitInterval) :
    ((lis x : ℕ) : ℝ≥0∞) ≤
        ENNReal.ofReal a + TalagrandConc.ConvexHull.fc (levelSet lis a) x * ENNReal.ofReal (Real.sqrt (lis x)) ∧
      ∀ v : ℝ, a + v ≤ (lis x : ℝ) →
        ENNReal.ofReal (v / Real.sqrt (a + v)) ≤ TalagrandConc.ConvexHull.fc (levelSet lis a) x := by sorry

end TalagrandConc.Subsequences
