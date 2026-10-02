-- Prove2me | Theorems.Thm_TheoryOfGames_Utility_segment_surjective
-- name    : TheoryOfGames.Utility.segment_surjective
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T01:11:32.936265+00:00
-- url     : https://prove2.me/theorems/97ad6402-d4e1-4d13-8a0d-247aa19ef0e0
-- title:
--   (A:C) — α ↦ (1 − α)u₀ + αv₀ maps 0 < α < 1 onto all of u₀ < w < v₀
-- statement:
--   Let $U$ be a system of utilities satisfying (3:A)–(3:C), and fix $u_0 < v_0$. Every utility $w$ with $u_0 < w < v_0$ is a combination of the endpoints: there is an $\alpha$ with $0 < \alpha < 1$ and
--   $$w = (1-\alpha)u_0 + \alpha v_0 .$$
--
--   This is the completeness half of the correspondence between the utility interval and the numerical interval $0 < \alpha < 1$; it is the step in which the axioms (3:B:c) and (3:B:d) enter.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), pp. 618–619, (A:C)

import Mathlib
import Definitions.Def_TheoryOfGames_Utility_UtilitySystem

namespace TheoryOfGames.Utility

/-- (A:C): for fixed `u₀ < v₀`, every `w` with `u₀ < w < v₀` is of the form
`(1 − α)u₀ + αv₀` for some `0 < α < 1`. -/
theorem segment_surjective {U : Type*} (S : UtilitySystem U) {u₀ v₀ : U}
    (h : S.lt u₀ v₀) :
    ∀ w : U, S.lt u₀ w → S.lt w v₀ → ∃ α : OpenUnit, S.cmb α u₀ v₀ = w := by sorry

end TheoryOfGames.Utility
