-- Prove2me | Theorems.Thm_TheoryOfGames_Decomposition_minimal_disjoint
-- name    : TheoryOfGames.Decomposition.minimal_disjoint
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T04:27:10.084826+00:00
-- url     : https://prove2.me/theorems/bb2da16d-ae51-4924-a14f-a118f5b3cb33
-- title:
--   (43:F) — any two different minimal splitting sets are disjunct
-- statement:
--   Let $v$ satisfy (42:6:a)–(42:6:c) on the finite set of players $I$. If $J_1$ and $J_2$ are minimal splitting sets with $J_1 \neq J_2$, then
--   $$J_1 \cap J_2 = \ominus.$$
--
--   Together with (43:G) this shows that the minimal splitting sets form a partition of $I$, the decomposition partition $\Pi_\Gamma$.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 355, 43.3.2, (43:F)

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
import Definitions.Def_TheoryOfGames_Decomposition_Splitting

namespace TheoryOfGames.Decomposition

/-- (43:F), 43.3.2: any two different minimal splitting sets are disjunct. -/
theorem minimal_disjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) (J₁ J₂ : Finset ι)
    (h₁ : IsMinimalSplitting v J₁) (h₂ : IsMinimalSplitting v J₂) (hne : J₁ ≠ J₂) :
    Disjoint J₁ J₂ := by sorry

end TheoryOfGames.Decomposition
