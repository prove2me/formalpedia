-- Prove2me | Theorems.Thm_WhittFLT_FirstPassage_firstPassage_runSup
-- name    : WhittFLT.FirstPassage.firstPassage_runSup
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:24:57.426063+00:00
-- url     : https://prove2.me/theorems/020fe6a7-2114-4653-ad2c-36a593b1a922
-- title:
--   Proof of Theorem 7.1 — reduction to nondecreasing paths: x↑ ∈ E and (x↑)⁻¹ = x⁻¹
-- statement:
--   Let $x\in E$ and $x^{\uparrow}(t)=\sup_{0\le s\le t}x(s)$. Then $x^{\uparrow}\in E$, and $x$ and its running supremum have the same first passage times:
--   $$(x^{\uparrow})^{-1}=x^{-1}.$$
--
--   This is the fact behind the sentence "It suffices to look at nondecreasing functions in $E$ because the supremum function is continuous ($M_1$)" in the proof of Theorem 7.1: $x^{\uparrow}$ is nondecreasing, and replacing $x$ by $x^{\uparrow}$ leaves the first passage time function unchanged.
--
--   **Formalization Note** The equality is stated as an equality of functions on all of $\mathbb R$; it holds at every level $t$ because $x^{\uparrow}(s)>t$ exactly when $x(u)>t$ for some $u\in[0,s]$.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), proof of Theorem 7.1, p. 82

import Mathlib
import Definitions.Def_WhittFLT_FirstPassage_FirstPassage

namespace WhittFLT.FirstPassage

open Set Filter Topology

/-- Whitt (1980), proof of Theorem 7.1, p. 82: "it suffices to look at nondecreasing functions in
`E`" — for `x ∈ E`, `x↑ ∈ E` and `(x↑)⁻¹ = x⁻¹`. -/
theorem firstPassage_runSup (x : ℝ → ℝ) (hx : InE x) :
    InE (WhittFLT.Reflection.runSup x) ∧ firstPassage (WhittFLT.Reflection.runSup x) = firstPassage x := by sorry

end WhittFLT.FirstPassage
