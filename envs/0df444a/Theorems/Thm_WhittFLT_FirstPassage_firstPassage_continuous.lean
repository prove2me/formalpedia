-- Prove2me | Theorems.Thm_WhittFLT_FirstPassage_firstPassage_continuous
-- name    : WhittFLT.FirstPassage.firstPassage_continuous
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:17.125493+00:00
-- url     : https://prove2.me/theorems/0bc4016d-75f5-462a-9239-a3943a7d2a1f
-- title:
--   Proof of Theorem 7.2 — for strictly increasing x ∈ E, x⁻¹ ∈ C (and x⁻¹(0) = 0)
-- statement:
--   Let $x\in E$ be strictly increasing on $[0,\infty)$. Then its first passage time function is continuous on $[0,\infty)$ and starts at $0$:
--   $$x^{-1}\in C([0,\infty),\mathbb R),\qquad x^{-1}(0)=0.$$
--
--   The path $x$ may jump; a jump of $x$ becomes a flat stretch of $x^{-1}$, and it is flat stretches of $x$ that would make $x^{-1}$ jump. This is the "Since $x^{-1}\in C$" step of the proof of Theorem 7.2.
--
--   **Formalization Note** The paper writes only $x^{-1}\in C$. The value $x^{-1}(0)=0$ is added to the conclusion because the next step (uniform convergence from $M_1$ convergence) needs it under the mission's origin convention $x(0-)=0$; it holds since $x(s)>x(0)\ge0$ for every $s>0$.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), proof of Theorem 7.2, p. 82

import Mathlib
import Definitions.Def_WhittFLT_FirstPassage_FirstPassage

namespace WhittFLT.FirstPassage

open Set Filter Topology

/-- Whitt (1980), proof of Theorem 7.2, p. 82: for strictly increasing `x ∈ E`, `x⁻¹ ∈ C`
(and `x⁻¹(0) = 0`). -/
theorem firstPassage_continuous (x : ℝ → ℝ) (hx : InE x) (hmono : StrictMonoOn x (Ici 0)) :
    ContinuousOn (firstPassage x) (Ici 0) ∧ firstPassage x 0 = 0 := by sorry

end WhittFLT.FirstPassage
