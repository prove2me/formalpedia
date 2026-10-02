-- Prove2me | Theorems.Thm_TheoryOfGames_Decomposition_constituent_indecomposable_iff
-- name    : TheoryOfGames.Decomposition.constituent_indecomposable_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T04:23:55.701286+00:00
-- url     : https://prove2.me/theorems/2d853489-4174-4b1e-9d72-2e3bad024b17
-- title:
--   (43:E) — the J-component is indecomposable iff J is a minimal splitting set
-- statement:
--   Let $v$ satisfy (42:6:a)–(42:6:c) on the finite set of players $I$, and let $J \neq \ominus$ be a splitting set of $\Gamma$ with $J$-constituent $\Delta$ ($v_\Delta(S) = v(S)$ for $S \subseteq J$). Then
--   $$\Delta \text{ is indecomposable} \iff J \text{ is a minimal splitting set of } \Gamma.$$
--
--   Consequently the elements of the decomposition partition $\Pi_\Gamma$ decompose $\Gamma$ into indecomposable constituents.
--
--   **Formalization Note** The book's constituent is a game, which has at least one player, so $J \neq \ominus$ is part of the hypothesis (for $J = \ominus$ the constituent would be the game with no players, which is trivially indecomposable, while $\ominus$ is not minimal by definition). The constituent is defined only for splitting sets $J$ (43.1), hence the hypothesis that $J$ is splitting.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 355, 43.3.2, (43:E)

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
import Definitions.Def_TheoryOfGames_Decomposition_Splitting
import Definitions.Def_TheoryOfGames_Decomposition_Constituent

namespace TheoryOfGames.Decomposition

/-- (43:E), 43.3.2: for a splitting set `J ≠ ⊖`, the `J`-component `Δ` (of `Γ`) is
indecomposable if and only if `J` is a minimal splitting set. -/
theorem constituent_indecomposable_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) (J : Finset ι) (hJ : IsSplitting v J)
    (hJne : J.Nonempty) :
    IsIndecomposable (constituent v J) ↔ IsMinimalSplitting v J := by sorry

end TheoryOfGames.Decomposition
