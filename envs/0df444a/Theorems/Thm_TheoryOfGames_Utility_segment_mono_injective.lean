-- Prove2me | Theorems.Thm_TheoryOfGames_Utility_segment_mono_injective
-- name    : TheoryOfGames.Utility.segment_mono_injective
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T01:07:41.686626+00:00
-- url     : https://prove2.me/theorems/ce0b9850-6a16-4ad1-b763-01694776bd49
-- title:
--   (A:B) — α ↦ (1 − α)u₀ + αv₀ is one-to-one and monotone into u₀ < w < v₀
-- statement:
--   Let $U$ be a system of utilities satisfying (3:A)–(3:C), and fix $u_0 < v_0$. Consider the mapping
--   $$\alpha \longmapsto w = (1-\alpha)u_0 + \alpha v_0, \qquad 0 < \alpha < 1 .$$
--   Then
--
--   1. every image lies in the interval: $u_0 < (1-\alpha)u_0 + \alpha v_0 < v_0$;
--   2. the mapping is one-to-one;
--   3. it is monotone: $\alpha < \beta$ implies $(1-\alpha)u_0 + \alpha v_0 < (1-\beta)u_0 + \beta v_0$.
--
--   Together with (A:C) this identifies the utility interval $u_0 < w < v_0$ with the numerical interval $0 < \alpha < 1$.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 618, (A:B)

import Mathlib
import Definitions.Def_TheoryOfGames_Utility_UtilitySystem

namespace TheoryOfGames.Utility

/-- (A:B): for fixed `u₀ < v₀`, the mapping `α ↦ (1 − α)u₀ + αv₀` maps `0 < α < 1` into the
interval `u₀ < w < v₀`, and it is one-to-one and monotone. -/
theorem segment_mono_injective {U : Type*} (S : UtilitySystem U) {u₀ v₀ : U}
    (h : S.lt u₀ v₀) :
    (∀ α : OpenUnit, S.lt u₀ (S.cmb α u₀ v₀) ∧ S.lt (S.cmb α u₀ v₀) v₀) ∧
      Function.Injective (fun α : OpenUnit => S.cmb α u₀ v₀) ∧
      ∀ α β : OpenUnit, (α : ℝ) < (β : ℝ) → S.lt (S.cmb α u₀ v₀) (S.cmb β u₀ v₀) := by sorry

end TheoryOfGames.Utility
