-- Prove2me | Theorems.Thm_WhitneyMatroid_Binary_c2_of_cStar
-- name    : WhitneyMatroid.Binary.c2_of_cStar
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:01:32.04633+00:00
-- url     : https://prove2.me/theorems/d91c6ff2-e699-4739-b8d6-14a288dd7232
-- title:
--   Appendix, p. 531 — Postulate (C₂) is a consequence of (C*)
-- statement:
--   Let $\mathcal C$ be any family of subsets ("circuits") of a finite set of elements that satisfies Postulate (C\*): every cycle (sum mod 2 of circuits) is a true sum of circuits. Then $\mathcal C$ satisfies Whitney's circuit postulate (C₂): if $P_1$ and $P_2$ are circuits, $e_1$ is in both $P_1$ and $P_2$, and $e_2$ is in $P_1$ but not in $P_2$, then there is a circuit
--
--   $$P_3 \subseteq P_1 \cup P_2 \quad\text{with}\quad e_2 \in P_3,\ e_1 \notin P_3.$$
--
--   Together with (C₁) ("no proper subset of a circuit is a circuit"), this shows that a family satisfying (C\*) is the family of circuits of a matroid, so (C\*) can serve as a postulate on top of (C₁).
--
--   **Formalization Note** Whitney's "$P_3$ in $P_1 + P_2$" uses $+$ for the union of sets (§8), and the statement is posed for an arbitrary family of sets, not for a Mathlib matroid, in which (C₂) already holds. No hypothesis besides (C\*) is assumed, as on the page. The ground type is finite, as Whitney's matroids are.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 531, Appendix (unnumbered: 'Postulate (C₂) is a consequence of (C*)'); (C₂) on p. 516, §8

import Mathlib
import Definitions.Def_WhitneyMatroid_Binary_Cycles

namespace WhitneyMatroid.Binary

/-- Appendix, p. 531: Postulate (C₂) is a consequence of (C*). For any family `𝒞` of sets
("circuits") satisfying (C*): if `P₁` and `P₂` are circuits, `e₁` is in both `P₁` and `P₂`, and
`e₂` is in `P₁` but not in `P₂`, then there is a circuit `P₃` in `P₁ + P₂` (the union) containing
`e₂` but not `e₁`. -/
theorem c2_of_cStar {α : Type*} [Finite α] (𝒞 : Set (Set α)) (hC : SatisfiesCStar 𝒞)
    (P₁ P₂ : Set α) (hP₁ : P₁ ∈ 𝒞) (hP₂ : P₂ ∈ 𝒞) (e₁ e₂ : α)
    (h₁₁ : e₁ ∈ P₁) (h₁₂ : e₁ ∈ P₂) (h₂₁ : e₂ ∈ P₁) (h₂₂ : e₂ ∉ P₂) :
    ∃ P₃ ∈ 𝒞, P₃ ⊆ P₁ ∪ P₂ ∧ e₂ ∈ P₃ ∧ e₁ ∉ P₃ := by sorry

end WhitneyMatroid.Binary
