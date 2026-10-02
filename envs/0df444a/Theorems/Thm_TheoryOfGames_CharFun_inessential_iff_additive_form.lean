-- Prove2me | Theorems.Thm_TheoryOfGames_CharFun_inessential_iff_additive_form
-- name    : TheoryOfGames.CharFun.inessential_iff_additive_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T04:04:16.636849+00:00
-- url     : https://prove2.me/theorems/4d40e7b2-fa14-42b2-825c-81f5cbf0c1b0
-- title:
--   (27:C) — Γ is inessential iff v(S) ≡ Σ_{k in S} α⁰_k for suitable α⁰
-- statement:
--   Let $v$ be a characteristic function on the subsets of $I = \{1, \dots, n\}$ (it satisfies (25:3:a)–(25:3:c)). Then the game is inessential if and only if there is a system of numbers $\alpha^0_1, \dots, \alpha^0_n$ with
--
--   $$v(S) \equiv \sum_{k \in S} \alpha^0_k \qquad \text{for all } S \subseteq I .$$
--
--   Inessential games are thus exactly those in which the value of every coalition arises additively from its members.
--
--   **Formalization Note** Players are `Fin n`. No condition $\sum_k \alpha^0_k = 0$ is imposed on the system, as on the page; it follows from $v(I) = 0$.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 251, 27.4.2, (27:C)

import Mathlib
import Definitions.Def_TheoryOfGames_CharFun_IsCharFunction
import Definitions.Def_TheoryOfGames_CharFun_StrategicEquivalence

namespace TheoryOfGames.CharFun

/-- (27:C): a game is inessential if and only if its characteristic function can be given the
form `v(S) ≡ ∑_{k ∈ S} α⁰_k` for a suitable system `α⁰₁, …, α⁰ₙ`. -/
theorem inessential_iff_additive_form {n : ℕ} (v : Finset (Fin n) → ℝ)
    (hv : IsCharFunction v) :
    IsInessential v ↔ ∃ α : Fin n → ℝ, ∀ S : Finset (Fin n), v S = ∑ k ∈ S, α k := by sorry

end TheoryOfGames.CharFun
