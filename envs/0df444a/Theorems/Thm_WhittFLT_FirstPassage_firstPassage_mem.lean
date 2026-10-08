-- Prove2me | Theorems.Thm_WhittFLT_FirstPassage_firstPassage_mem
-- name    : WhittFLT.FirstPassage.firstPassage_mem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:24:48.462009+00:00
-- url     : https://prove2.me/theorems/cbc2fa0c-5714-464f-8a17-5b360a0b99ca
-- title:
--   §7 — for x ∈ E, x⁻¹ ∈ E ∩ D₀([0, ∞), [0, ∞))
-- statement:
--   Let $x\in E$: $x\in D([0,\infty),\mathbb R)$, unbounded above, with $x(0)\ge0$. Then its first passage time function $x^{-1}(t)=\inf\{s\ge0:x(s)>t\}$ satisfies
--   $$x^{-1}\in E\cap D_0([0,\infty),[0,\infty)),$$
--   that is, $x^{-1}$ is càdlàg on $[0,\infty)$, unbounded above, nonnegative at $0$, nondecreasing on $[0,\infty)$, and maps $[0,\infty)$ into $[0,\infty)$.
--
--   This places the first passage time map inside the spaces on which Theorems 7.1 and 7.2 state its continuity.
--
--   **Formalization Note** $D_0([0,\infty),[0,\infty))$ is written as "càdlàg on $[0,\infty)$, monotone on $[0,\infty)$, maps $[0,\infty)$ into $[0,\infty)$" (the paper's $D_0(T_1,T_2)$, p. 74, is the nondecreasing $T_2$-valued paths in $D$).
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), §7, p. 82

import Mathlib
import Definitions.Def_WhittFLT_FirstPassage_FirstPassage

namespace WhittFLT.FirstPassage

open Set Filter Topology

/-- Whitt (1980), §7, p. 82: for `x ∈ E`, `x⁻¹ ∈ E ∩ D₀([0, ∞), [0, ∞))`. -/
theorem firstPassage_mem (x : ℝ → ℝ) (hx : InE x) :
    InE (firstPassage x) ∧ MonotoneOn (firstPassage x) (Ici 0) ∧
      MapsTo (firstPassage x) (Ici 0) (Ici 0) := by sorry

end WhittFLT.FirstPassage
