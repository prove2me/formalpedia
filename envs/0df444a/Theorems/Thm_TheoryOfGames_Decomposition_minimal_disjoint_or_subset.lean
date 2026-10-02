-- Prove2me | Theorems.Thm_TheoryOfGames_Decomposition_minimal_disjoint_or_subset
-- name    : TheoryOfGames.Decomposition.minimal_disjoint_or_subset
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T04:31:20.261616+00:00
-- url     : https://prove2.me/theorems/274eda32-f472-4472-bec5-971fb335f160
-- title:
--   (43:I) — a minimal splitting set is disjunct with, or contained in, any splitting set K
-- statement:
--   Let $v$ satisfy (42:6:a)–(42:6:c) on the finite set of players $I$, and let $K$ be a splitting set. Then every minimal splitting set $J$ is either disjunct with $K$ or contained in $K$:
--   $$J \cap K = \ominus \quad\text{or}\quad J \subseteq K.$$
--
--   This is the step of the proof of (43:H) that places each block of $\Pi_\Gamma$ on one side of a splitting set.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 356, 43.3.2, proof of (43:H), (43:I)

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
import Definitions.Def_TheoryOfGames_Decomposition_Splitting

namespace TheoryOfGames.Decomposition

/-- (43:I), 43.3.2: for a splitting set `K`, every minimal splitting set `J` is either disjunct
with `K` or `⊆ K`. -/
theorem minimal_disjoint_or_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) (K : Finset ι) (hK : IsSplitting v K)
    (J : Finset ι) (hJ : IsMinimalSplitting v J) :
    Disjoint J K ∨ J ⊆ K := by sorry

end TheoryOfGames.Decomposition
