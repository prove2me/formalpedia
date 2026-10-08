-- Prove2me | Theorems.Thm_WhittFLT_FirstPassage_runSup_m1_continuous
-- name    : WhittFLT.FirstPassage.runSup_m1_continuous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:21.708984+00:00
-- url     : https://prove2.me/theorems/b4c86173-33aa-4e22-a73c-86d36810758a
-- title:
--   §6 and proof of Theorem 7.1 — the supremum function is continuous (M₁)
-- statement:
--   Let $x_n$, $n\ge1$, and $x$ be real-valued paths on $[0,\infty)$ with $x_n(0)\ge0$ and $x(0)\ge0$, and let $x^{\uparrow}(t)=\sup_{0\le s\le t}x(s)$. If $x_n\to x$ in $M_1$, then
--   $$x_n^{\uparrow}\to x^{\uparrow}\quad(M_1).$$
--
--   The proof of Theorem 7.1 uses this to reduce the first passage time map to nondecreasing paths.
--
--   **Formalization Note** The paper states on p. 80 that "The supremum function $\uparrow$ is easily seen to be continuous in each of Skorohod's (1956) topologies", for all of $D$ and Skorohod's $M_1$. The mission's $M_1$ uses the origin convention $x(0-)=0$ (needed for Theorem 7.1), and under that convention the supremum is not continuous on all of $D$: for $x\equiv-1$ and $x_n=0$ on $[0,1/n)$, $-1$ afterwards, $x_n\to x(M_1)$ but $x_n^{\uparrow}\equiv0$ while $x^{\uparrow}\equiv-1$. We therefore state the form the proof of Theorem 7.1 uses ("because the supremum function is continuous ($M_1$)", applied to paths in $E$), with the hypothesis $x_n(0),x(0)\ge0$ that every path of $E$ satisfies. The general sentence of p. 80 is not stated.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), §6, p. 80; proof of Theorem 7.1, p. 82

import Mathlib
import Definitions.Def_WhittFLT_FirstPassage_FirstPassage
import Definitions.Def_WhittFLT_FirstPassage_M1

namespace WhittFLT.FirstPassage

open Set Filter Topology

/-- Whitt (1980), §6, p. 80, and proof of Theorem 7.1, p. 82: the supremum function is continuous
(`M₁`), for paths with nonnegative initial value (as on `E`). -/
theorem runSup_m1_continuous (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ)
    (hxs0 : ∀ n, 0 ≤ xs n 0) (hx0 : 0 ≤ x 0) (h : M1Tendsto xs x) :
    M1Tendsto (fun n => WhittFLT.Reflection.runSup (xs n)) (WhittFLT.Reflection.runSup x) := by sorry

end WhittFLT.FirstPassage
