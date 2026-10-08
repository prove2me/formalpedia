-- Prove2me | Theorems.Thm_WhittFLT_FirstPassage_theorem_7_4
-- name    : WhittFLT.FirstPassage.theorem_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:24:55.410658+00:00
-- url     : https://prove2.me/theorems/d78c3adb-529d-4ec0-a1f6-bf7ff8bc8f35
-- title:
--   Theorem 7.4 — joint J₁ convergence of centered suprema and first passage times forces x ∈ C
-- statement:
--   Let $c_n\to\infty$, let $x_n\in E$ for every $n$, and let $e(t)=t$ be the identity. If
--   $$c_n(x_n^{\uparrow}-e)\to x\ (J_1)\qquad\text{and}\qquad c_n(x_n^{-1}-e)\to -x\ (J_1)$$
--   in $D([0,\infty),\mathbb R)$, then $x$ is continuous: $x\in C$.
--
--   The paper introduces it with "the following result shows that $x\in C$ is necessary if we want convergence for both the supremum and first passage times".
--
--   **Formalization Note** "$x\in C$" is continuity on $[0,\infty)$ (within $[0,\infty)$ at the origin). The convergences are sequential, in the $J_1$ topology of the definition file.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), Theorem 7.4, p. 83

import Mathlib
import Definitions.Def_WhittFLT_FirstPassage_FirstPassage

namespace WhittFLT.FirstPassage

open Set Filter Topology

/-- Whitt (1980), Theorem 7.4, p. 83: if `cₙ → ∞`, `xₙ ∈ E`, `cₙ(xₙ↑ − e) → x (J₁)` and
`cₙ(xₙ⁻¹ − e) → −x (J₁)`, then `x ∈ C`. -/
theorem theorem_7_4 (c : ℕ → ℝ) (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ)
    (hc : Tendsto c atTop atTop) (hxs : ∀ n, InE (xs n))
    (hsup : WhittFLT.Composition.J1Tendsto (Ici 0) (fun n t => c n * (WhittFLT.Reflection.runSup (xs n) t - t)) x)
    (hinv : WhittFLT.Composition.J1Tendsto (Ici 0) (fun n t => c n * (firstPassage (xs n) t - t)) (fun t => -x t)) :
    ContinuousOn x (Ici 0) := by sorry

end WhittFLT.FirstPassage
