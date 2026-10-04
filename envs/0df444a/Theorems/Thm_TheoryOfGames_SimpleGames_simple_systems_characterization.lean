-- Prove2me | Theorems.Thm_TheoryOfGames_SimpleGames_simple_systems_characterization
-- name    : TheoryOfGames.SimpleGames.simple_systems_characterization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T04:58:36.614487+00:00
-- url     : https://prove2.me/theorems/44c2af83-46c2-4251-9674-f2b6bb996f7c
-- title:
--   (49:F) — the systems W, L of simple games are characterized by (48:A:a)–(48:A:d), (49:C)
-- statement:
--   Let $n$ be a number of players, $I = \{1, \dots, n\}$, and let $W, L$ be two systems of subsets of $I$. There is a simple zero-sum $n$-person game $\Gamma$ — a characteristic function $v$ with (25:3:a)–(25:3:c) which is simple (49.4) — with $W_\Gamma = W$ and $L_\Gamma = L$ if and only if
--
--   1. (48:A:a) $W$ and $L$ are complementary sets in $\bar I$;
--   2. (48:A:b) complementation in $I$ maps $W$ and $L$ on each other: $S \in W$ iff $-S \in L$;
--   3. (48:A:c) $W$ contains all supersets of its elements;
--   4. (48:A:d) $L$ contains all subsets of its elements;
--   5. (49:C) $L$ contains the empty set and all one-element sets.
--
--   By this result the theory of simple games is coextensive with the theory of such pairs of systems $W, L$ (49.6.1).
--
--   **Formalization Note** A "game" is represented by its characteristic function, as in the whole chapter; by 26.1 every $v$ with (25:3:a)–(25:3:c) is the characteristic function of a zero-sum game. No normalization is imposed on $v$.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 429, (49:F); p. 421, (48:A:a)–(48:A:d); p. 425, (49:C)

import Mathlib
import Definitions.Def_TheoryOfGames_SimpleGames_WinningLosing

namespace TheoryOfGames.SimpleGames

/-- (49:F), p. 429: in order that two given systems `W, L (⊆ Ī)` be the `W_Γ, L_Γ` of a suitable
simple game `Γ`, these requirements are necessary and sufficient: (48:A:a)–(48:A:d), (49:C).
* (48:A:a) `W` and `L` are complementary sets in `Ī`;
* (48:A:b) complementation (in `I`) maps `W` and `L` on each other;
* (48:A:c) `W` contains all supersets of its elements;
* (48:A:d) `L` contains all subsets of its elements;
* (49:C) `L` contains the empty set and all one-element sets. -/
theorem simple_systems_characterization {n : ℕ} (W L : Set (Finset (Fin n))) :
    (∃ v : Finset (Fin n) → ℝ, IsCharFunction v ∧ IsSimple v ∧
        winningSets v = W ∧ losingSets v = L) ↔
      ((∀ S : Finset (Fin n), S ∈ W ↔ S ∉ L) ∧
        (∀ S : Finset (Fin n), S ∈ W ↔ Sᶜ ∈ L) ∧
        (∀ S T : Finset (Fin n), S ∈ W → S ⊆ T → T ∈ W) ∧
        (∀ S T : Finset (Fin n), S ∈ L → T ⊆ S → T ∈ L) ∧
        (∅ ∈ L ∧ ∀ i : Fin n, ({i} : Finset (Fin n)) ∈ L)) := by sorry

end TheoryOfGames.SimpleGames
