-- Prove2me | Theorems.Thm_TheoryOfGames_Decomposition_constituent_splitting_iff
-- name    : TheoryOfGames.Decomposition.constituent_splitting_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T04:22:59.335406+00:00
-- url     : https://prove2.me/theorems/16c8ed85-fa8e-406c-9436-5a43ec4429c4
-- title:
--   (43:D) — for a splitting set J, a J′ ⊆ J splits the J-constituent iff it splits Γ
-- statement:
--   Let $v$ satisfy (42:6:a)–(42:6:c) on the finite set of players $I$, let $J$ be a splitting set of $\Gamma$, and let $\Delta$ be the $J$-constituent of $\Gamma$, the game on the set of players $J$ with $v_\Delta(S) = v(S)$ for $S \subseteq J$. Then for every $J' \subseteq J$:
--   $$J' \text{ is a splitting set of } \Delta \iff J' \text{ is a splitting set of } \Gamma.$$
--   Here "splitting set of $\Delta$" refers to the complement $J - J'$ inside $J$, and "splitting set of $\Gamma$" to the complement $I - J'$.
--
--   To be self-contained within a self-contained set is the same as to be self-contained in the whole set of players.
--
--   **Formalization Note** $J'$ is a `Finset` of the subtype `↥J` (a set of players of $\Delta$); its image in $I$ is `J'.map (Function.Embedding.subtype _)`.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 355, 43.3.1, (43:D)

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
import Definitions.Def_TheoryOfGames_Decomposition_Splitting
import Definitions.Def_TheoryOfGames_Decomposition_Constituent

namespace TheoryOfGames.Decomposition

/-- (43:D), 43.3.1: consider a splitting set `J` of `Γ` and the `J`-constituent `Δ` of `Γ`. Then a
`J′ ⊆ J` is a splitting set of `Δ` if and only if it is one of `Γ`. Here `J′` is a set of players
of `Δ`, i.e. a `Finset` of the subtype `↥J`, and its image in `I` is `J′.map (subtype)`. -/
theorem constituent_splitting_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) (J : Finset ι) (hJ : IsSplitting v J)
    (J' : Finset J) :
    IsSplitting (constituent v J) J' ↔
      IsSplitting v (J'.map (Function.Embedding.subtype (· ∈ J))) := by sorry

end TheoryOfGames.Decomposition
