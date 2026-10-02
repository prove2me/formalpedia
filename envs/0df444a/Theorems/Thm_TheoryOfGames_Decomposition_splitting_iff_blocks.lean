-- Prove2me | Theorems.Thm_TheoryOfGames_Decomposition_splitting_iff_blocks
-- name    : TheoryOfGames.Decomposition.splitting_iff_blocks
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T04:34:35.64322+00:00
-- url     : https://prove2.me/theorems/8607813d-b5e0-471e-9bb0-1746f026c87c
-- title:
--   (43:H*) — K is splitting iff each element of Π_Γ lies inside or outside K
-- statement:
--   Let $v$ satisfy (42:6:a)–(42:6:c) on the finite set of players $I$, and let $\Pi_\Gamma$ be the decomposition partition (the system of minimal splitting sets). A set $K \subseteq I$ is a splitting set if and only if the points of each element of $\Pi_\Gamma$ go together as far as $K$ is concerned:
--   $$K \text{ splitting} \iff \text{for every } J \in \Pi_\Gamma:\ J \subseteq K \ \text{or}\ J \cap K = \ominus.$$
--
--   This is the restatement of (43:H) in terms of the partition $\Pi_\Gamma$.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 356, 43.3.3, (43:H*)

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
import Definitions.Def_TheoryOfGames_Decomposition_Splitting

namespace TheoryOfGames.Decomposition

/-- (43:H*), 43.3.3: a set `K ⊆ I` is a splitting set if and only if each element of the
decomposition partition `Π_Γ` lies completely inside or completely outside of `K`. -/
theorem splitting_iff_blocks {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) (K : Finset ι) :
    IsSplitting v K ↔ ∀ J ∈ decompositionPartition v, J ⊆ K ∨ Disjoint J K := by sorry

end TheoryOfGames.Decomposition
