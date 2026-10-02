-- Prove2me | Theorems.Thm_TheoryOfGames_SimpleGames_disjoint_iff_essential
-- name    : TheoryOfGames.SimpleGames.disjoint_iff_essential
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T04:55:42.23146+00:00
-- url     : https://prove2.me/theorems/a8168d22-8641-46c2-98fd-a4cdb0155b4d
-- title:
--   (49:B) — W_Γ ∩ L_Γ = ⊖ iff Γ is essential; W_Γ = L_Γ = Ī if Γ is inessential
-- statement:
--   Let $v$ be a characteristic function (25:3:a)–(25:3:c) of a zero-sum $n$-person game $\Gamma$, with winning and losing coalitions $W_\Gamma$, $L_\Gamma$ as in (49:W), (49:L).
--
--   1. (49:B:a) The condition
--   $$\text{(49:1:a)}\qquad W_\Gamma \cap L_\Gamma = \ominus$$
--   holds if and only if $\Gamma$ is essential.
--   2. (49:B:b) If $\Gamma$ is inessential, then $W_\Gamma = L_\Gamma = \bar I$, the system of all subsets of $I$.
--
--   Together with (49:1:b) this is what separates the simple games (49.4) from general ones: in an essential game no coalition is both winning and losing.
--
--   **Formalization Note** "Essential" is the negation of `IsInessential v` (reduced form identically zero, 27.3.1).
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 424, (49:B), (49:1:a)

import Mathlib
import Definitions.Def_TheoryOfGames_SimpleGames_WinningLosing

namespace TheoryOfGames.SimpleGames

/-- (49:B), p. 424: (49:B:a) (49:1:a) `W_Γ ∩ L_Γ = ⊖` holds if and only if `Γ` is essential;
(49:B:b) if `Γ` is inessential, then `W_Γ = L_Γ = Ī`. -/
theorem disjoint_iff_essential {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v) :
    ((∀ S : Finset (Fin n), ¬ (S ∈ winningSets v ∧ S ∈ losingSets v)) ↔ ¬ IsInessential v) ∧
    (IsInessential v → winningSets v = Set.univ ∧ losingSets v = Set.univ) := by sorry

end TheoryOfGames.SimpleGames
