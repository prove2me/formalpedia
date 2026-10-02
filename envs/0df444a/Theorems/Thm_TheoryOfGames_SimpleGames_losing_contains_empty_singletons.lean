-- Prove2me | Theorems.Thm_TheoryOfGames_SimpleGames_losing_contains_empty_singletons
-- name    : TheoryOfGames.SimpleGames.losing_contains_empty_singletons
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T04:48:17.576061+00:00
-- url     : https://prove2.me/theorems/d6b6d9fb-c2a8-4ee1-9b00-456a234c39ec
-- title:
--   (49:C) — L_Γ contains the empty set and all one-element sets
-- statement:
--   Let $v$ be a characteristic function (25:3:a)–(25:3:c) of a zero-sum $n$-person game $\Gamma$ and $L_\Gamma$ the set of its flat (losing) coalitions (49:L). Then
--   $$\ominus \in L_\Gamma \quad\text{and}\quad (i) \in L_\Gamma \text{ for every player } i.$$
--
--   This is the property of the losing coalitions which does not follow from (48:A:a)–(48:A:d): a coalition of one player is always defeated. It is one of the conditions characterizing the systems $W_\Gamma, L_\Gamma$ in (49:E) and (49:F).
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 425, (49:C)

import Mathlib
import Definitions.Def_TheoryOfGames_SimpleGames_WinningLosing

namespace TheoryOfGames.SimpleGames

/-- (49:C), p. 425: `L_Γ` contains the empty set and all one-element sets. -/
theorem losing_contains_empty_singletons {n : ℕ} (v : Finset (Fin n) → ℝ)
    (hv : IsCharFunction v) :
    ∅ ∈ losingSets v ∧ ∀ i : Fin n, ({i} : Finset (Fin n)) ∈ losingSets v := by sorry

end TheoryOfGames.SimpleGames
