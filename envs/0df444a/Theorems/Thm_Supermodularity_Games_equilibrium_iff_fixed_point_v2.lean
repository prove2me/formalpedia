-- Prove2me | Theorems.Thm_Supermodularity_Games_equilibrium_iff_fixed_point_v2
-- name    : Supermodularity.Games.equilibrium_iff_fixed_point_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:42.303063+00:00
-- url     : https://prove2.me/theorems/2e747d04-f34f-4588-b0ea-d6abb764834e
-- title:
--   Lemma 4.2.1 - equilibrium points are the fixed points of the best joint response (corrected: nonempty set of players)
-- statement:
--   Let $(N, S, \{f_i\}_{i\in N})$ be a noncooperative game: $N$ is a finite, **nonempty** set of players, player $i$'s strategies are vectors in $\mathbb{R}^{m_i}$, $S \subseteq \prod_{i\in N}\mathbb{R}^{m_i}$ is the feasible joint strategy set and $f_i$ is player $i$'s payoff function. For a joint strategy $x$ write $S_i(x_{-i}) = \{y_i : (y_i, x_{-i}) \in S\}$ for player $i$'s feasible section,
--   $$Y_i(x_{-i}) = \arg\max_{y_i \in S_i(x_{-i})} f_i(y_i, x_{-i})$$
--   for the best response set, and $Y(x) = \prod_{i\in N} Y_i(x_{-i})$ for the best joint response correspondence. A joint strategy $x'$ is an *equilibrium point* if $x' \in S$ and $f_i(x') \ge f_i(y_i, x'_{-i})$ for every $y_i \in S_i(x'_{-i})$ and every $i \in N$.
--
--   Then, for every joint strategy $x'$,
--   $$x' \text{ is an equilibrium point} \quad\Longleftrightarrow\quad x' \in Y(x'),$$
--   that is, the set of all equilibrium points of the game is identical to the set of fixed points of $Y$ (Lemma 4.2.1). This reduces the existence of an equilibrium point to a lattice fixed-point problem, which is how Theorem 2.5.1 (Zhou's theorem) enters the theory of supermodular games.
--
--   **Formalization Note.** The retired version quantified over an arbitrary finite player type, including the empty one, for which $x' \in Y(x')$ is vacuous while an equilibrium point must still be feasible, so the equivalence failed for $S = \emptyset$. The new statement assumes the set of players is nonempty (`[Nonempty ι]`), the standing convention for a noncooperative game in Chapter 4; with at least one player $i$, $x'_i \in Y_i(x'_{-i})$ already forces $x' \in S$, so the biconditional holds at every joint strategy $x'$ and is exactly the extensional identity of the two sets. As throughout the mission, strategies are vectors in $\mathbb{R}^{m_i}$ and the other players' strategies enter through the profile $x'$ with its $i$-th coordinate overwritten. No other change.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 1998 (reprint 2011), p. 179-180, Lemma 4.2.1 (with the chapter's standing assumption that the game has at least one player made explicit)

import Mathlib
import Definitions.Def_Supermodularity_Games_IsEquilibrium
import Definitions.Def_Supermodularity_Games_BestJointResponse

namespace Supermodularity.Games

/-- Lemma 4.2.1 (Topkis, *Supermodularity and Complementarity*, p. 179–180). For a
noncooperative game with a (finite, nonempty) set of players `ι`, feasible joint strategy
set `S` and payoffs `f`, the set of equilibrium points is identical to the set of fixed
points of the best joint response correspondence `Y`: `x'` is an equilibrium point iff
`x' ∈ Y(x')`.

Corrected version of `equilibrium_iff_fixed_point`: the retired statement allowed an empty
set of players, for which `x' ∈ Y(x')` is vacuous while `IsEquilibrium` still demands
`x' ∈ S`; the book's game has at least one player (`[Nonempty ι]`), and then
`x' ∈ Y(x')` already forces `x' ∈ S`, so the equivalence holds for every `x'`. -/
theorem equilibrium_iff_fixed_point_v2 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {m : ι → ℕ}
    (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (x' : ∀ i, Fin (m i) → ℝ) :
    IsEquilibrium S f x' ↔ x' ∈ BestJointResponse S f x' := by sorry

end Supermodularity.Games
