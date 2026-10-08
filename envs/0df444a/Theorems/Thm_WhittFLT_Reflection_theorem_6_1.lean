-- Prove2me | Theorems.Thm_WhittFLT_Reflection_theorem_6_1
-- name    : WhittFLT.Reflection.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:50.999132+00:00
-- url     : https://prove2.me/theorems/a9fcf053-e7e5-4288-8451-b199955d00c4
-- title:
--   Theorem 6.1 — the running supremum is 1-Lipschitz in J₁ distance
-- statement:
--   For $b>0$ and real càdlàg paths $x,y$ on $[0,b]$, let $d$ be the $J_1$ metric of equation (2.1). Then
--
--   $$
--   d(x^{\uparrow},y^{\uparrow})\le d(x,y).
--   $$
--
--   This quantitative continuity result is used for the finite-drift case of the running-supremum limit.
--
--   **Formalization Note** This states the compact case using metric (2.1). The paper also mentions the noncompact metric (2.2), which is outside this mission’s definition layer. The distance is represented in the extended nonnegative reals.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), Theorem 6.1, p. 80; metric (2.1), p. 70

import Mathlib
import Definitions.Def_WhittFLT_Reflection_Supremum

namespace WhittFLT.Reflection

open Set Filter Topology

/-- Whitt (1980), Theorem 6.1, p. 80, for the compact metric (2.1). -/
theorem theorem_6_1 (b : ℝ) (hb : 0 < b) (x y : ℝ → ℝ)
    (hx : WhittFLT.Composition.IsCadlagOn (Icc 0 b) x) (hy : WhittFLT.Composition.IsCadlagOn (Icc 0 b) y) :
    WhittFLT.Composition.j1Dist 0 b (runSup x) (runSup y) ≤ WhittFLT.Composition.j1Dist 0 b x y := by sorry

end WhittFLT.Reflection
