-- Prove2me | Theorems.Thm_TheoryOfGames_SimpleGames_winning_losing_48A_bcd
-- name    : TheoryOfGames.SimpleGames.winning_losing_48A_bcd
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T04:50:49.24176+00:00
-- url     : https://prove2.me/theorems/6e83dca5-17cf-4a68-8abc-617f8326dcc1
-- title:
--   (49:A) — W_Γ, L_Γ always fulfill (48:A:b)–(48:A:d)
-- statement:
--   Let $v$ be a characteristic function (25:3:a)–(25:3:c) of a zero-sum $n$-person game $\Gamma$, with winning and losing coalitions $W_\Gamma$, $L_\Gamma$ as in (49:W), (49:L). Then
--
--   1. (48:A:b) complementation in $I$ maps $W_\Gamma$ and $L_\Gamma$ on each other: $S \in W_\Gamma$ if and only if $-S \in L_\Gamma$;
--   2. (48:A:c) $W_\Gamma$ contains all supersets of its elements;
--   3. (48:A:d) $L_\Gamma$ contains all subsets of its elements.
--
--   No normalization and no simplicity is assumed. What can fail in a general game is only (48:A:a), the complementarity of $W_\Gamma$ and $L_\Gamma$, whose two halves are the subject of (49:B) and of the definition of simplicity.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 424, (49:A); p. 421, (48:A:b)–(48:A:d)

import Mathlib
import Definitions.Def_TheoryOfGames_SimpleGames_WinningLosing

namespace TheoryOfGames.SimpleGames

/-- (49:A), p. 424: `W_Γ`, `L_Γ` always fulfill (48:A:b)–(48:A:d):
(48:A:b) complementation (in `I`) maps `W_Γ` and `L_Γ` on each other;
(48:A:c) `W_Γ` contains all supersets of its elements;
(48:A:d) `L_Γ` contains all subsets of its elements. -/
theorem winning_losing_48A_bcd {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v) :
    (∀ S : Finset (Fin n), S ∈ winningSets v ↔ Sᶜ ∈ losingSets v) ∧
    (∀ S T : Finset (Fin n), S ∈ winningSets v → S ⊆ T → T ∈ winningSets v) ∧
    (∀ S T : Finset (Fin n), S ∈ losingSets v → T ⊆ S → T ∈ losingSets v) := by sorry

end TheoryOfGames.SimpleGames
