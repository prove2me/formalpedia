-- Prove2me | Theorems.Thm_WhittFLT_FirstPassage_theorem_7_1
-- name    : WhittFLT.FirstPassage.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:28.247486+00:00
-- url     : https://prove2.me/theorems/d9f654f4-4afa-4a47-90e4-f4d11d5f3873
-- title:
--   Theorem 7.1 — the first passage time function from E(M₁) into E ∩ D₀(M₁) is continuous
-- statement:
--   Let $x_n$, $n\ge1$, and $x$ be elements of $E$ (paths in $D([0,\infty),\mathbb R)$, unbounded above, with nonnegative initial value). If $x_n\to x$ in $M_1$, then their first passage time functions converge in $M_1$:
--   $$x_n\to x\ (M_1)\quad\Longrightarrow\quad x_n^{-1}\to x^{-1}\ (M_1).$$
--
--   This is the continuity of the first passage time map in Skorohod's $M_1$ topology, the main tool of §7: with Theorem 7.1, a functional limit theorem for a cumulative process yields one for its first passage times (Whitt 1971).
--
--   **Formalization Note** The page states continuity of the map $E(M_1)\to E\cap D_0(M_1)$; it is formalized sequentially (the $M_1$ topology on $D$ is metrizable). The $M_1$ topology is the mission's, with the convention $x(0-)=0$ at the origin. With the convention $x(0-)=x(0)$ the theorem is false: $x(s)=(s-1)^+$, $x_n=x+1/n$ gives $x_n^{-1}(t)=0$ for $t<1/n$ but $x^{-1}(0)=1$. The convention is the fix, not an extra hypothesis such as $x(0)=0$, which would give a weaker theorem than the paper's.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), Theorem 7.1, p. 82

import Mathlib
import Definitions.Def_WhittFLT_FirstPassage_FirstPassage
import Definitions.Def_WhittFLT_FirstPassage_M1

namespace WhittFLT.FirstPassage

open Set Filter Topology

/-- Whitt (1980), Theorem 7.1, p. 82: the first passage time function mapping `E(M₁)` into
`E ∩ D₀(M₁)` is continuous (with the origin convention `x(0−) = 0` of `M1Tendsto`). -/
theorem theorem_7_1 (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ)
    (hxs : ∀ n, InE (xs n)) (hx : InE x) (h : M1Tendsto xs x) :
    M1Tendsto (fun n => firstPassage (xs n)) (firstPassage x) := by sorry

end WhittFLT.FirstPassage
