-- Prove2me | Theorems.Thm_TheoryOfGames_SimpleGames_undominated_iff_mem_uPlus
-- name    : TheoryOfGames.SimpleGames.undominated_iff_mem_uPlus
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T05:06:16.111727+00:00
-- url     : https://prove2.me/theorems/f5acaa1c-1380-4c49-a41c-98b2f58e63bf
-- title:
--   (50:G) — β is undominated by V = {α^S : S ∈ U} iff R(β) ∈ U⁺
-- statement:
--   Let $v$ be the characteristic function (25:3:a)–(25:3:c) of a simple game in the reduced form with $\gamma = 1$, so $v((i)) = -1$ for every player $i$ (50.4.1). Let $U \subseteq W^m_\Gamma$ be a set of minimal winning coalitions and $x_1, \dots, x_n$ numbers with
--   $$\text{(50:7)}\ \ x_i \geqq 0, \qquad \text{(50:8)}\ \ \sum_{i \in S} x_i = n \text{ when } S \text{ is in } U,$$
--   and let $V$ be the set of the imputations $\vec\alpha^S$, $S$ in $U$ ($\alpha^S_i = -1$ for $i \notin S$, $-1 + x_i$ for $i \in S$). Let $U^*$ be the set of all $R \subseteq I$ which possess a subset belonging to $U$, $U^+$ the set of all $R$ for which $-R$ does not belong to $U^*$, and $R(\vec\beta)$ the set of all $i$ with $\beta_i \geqq -1 + x_i$ (50:11).
--
--   Then for every imputation $\vec\beta$: $\vec\beta$ is undominated by any element of $V$ if and only if $R(\vec\beta)$ belongs to $U^+$.
--
--   This reduces the solution property of $V$ to a combinatorial condition on $U$ and the $x_i$, and is the step from which (50:I) and (50:J) are derived.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 439, (50:G); p. 438, 50.5.1, (50:7), (50:8); p. 436, 50.4.1 (reduced form, γ = 1)

import Mathlib
import Definitions.Def_TheoryOfGames_SimpleGames_Majority

namespace TheoryOfGames.SimpleGames

/-- (50:G), p. 439: for a simple game in the reduced form with `γ = 1` (`v((i)) = -1`), a set
`U ⊆ W^m` and numbers `xᵢ` with (50:7) `xᵢ ≧ 0` and (50:8) `∑_{i in S} xᵢ = n` for `S` in
`U`, let `V` be the set of the `α^S`, `S` in `U`. Then an imputation `β` is undominated by
any element of `V` if and only if `R(β)` belongs to `U⁺`. -/
theorem undominated_iff_mem_uPlus {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v)
    (hs : IsSimple v) (hred : ∀ i : Fin n, v {i} = -1)
    (U : Set (Finset (Fin n))) (hU : U ⊆ minimalSets (winningSets v))
    (x : Fin n → ℝ) (hx7 : ∀ i, 0 ≤ x i) (hx8 : ∀ S ∈ U, ∑ i ∈ S, x i = (n : ℝ))
    (β : Fin n → ℝ) (hβ : IsImputation v β) :
    (∀ α ∈ mainSet U x, ¬ Dominates v α β) ↔ rSet x β ∈ uPlus U := by sorry

end TheoryOfGames.SimpleGames
