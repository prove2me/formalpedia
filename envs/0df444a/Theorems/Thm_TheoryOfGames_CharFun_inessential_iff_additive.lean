-- Prove2me | Theorems.Thm_TheoryOfGames_CharFun_inessential_iff_additive
-- name    : TheoryOfGames.CharFun.inessential_iff_additive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T04:06:34.851847+00:00
-- url     : https://prove2.me/theorems/3639b84e-aa68-48b8-b590-ce2a085fdb15
-- title:
--   (27:D) — Γ is inessential iff (25:3:c) always holds with equality
-- statement:
--   Let $v$ be a characteristic function on the subsets of $I = \{1, \dots, n\}$ (it satisfies (25:3:a)–(25:3:c)). Then the game is inessential if and only if $v$ always has $=$ in (25:3:c), i.e.
--
--   $$v(S \cup T) = v(S) + v(T) \qquad \text{whenever } S \cap T = \ominus .$$
--
--   Together with (27:C) this identifies inessentiality with additivity of the characteristic function.
--
--   **Formalization Note** Players are `Fin n`, coalitions `Finset (Fin n)`; $S \cap T = \ominus$ is `Disjoint S T`.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 251, 27.4.2, (27:D)

import Mathlib
import Definitions.Def_TheoryOfGames_CharFun_IsCharFunction
import Definitions.Def_TheoryOfGames_CharFun_StrategicEquivalence

namespace TheoryOfGames.CharFun

/-- (27:D): a game is inessential if and only if its characteristic function has always `=` in
(25:3:c), i.e. `v(S ∪ T) = v(S) + v(T)` whenever `S ∩ T = ∅`. -/
theorem inessential_iff_additive {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v) :
    IsInessential v ↔ ∀ S T : Finset (Fin n), Disjoint S T → v (S ∪ T) = v S + v T := by sorry

end TheoryOfGames.CharFun
