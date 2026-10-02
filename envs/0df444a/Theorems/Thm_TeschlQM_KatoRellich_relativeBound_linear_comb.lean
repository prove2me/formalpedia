-- Prove2me | Theorems.Thm_TeschlQM_KatoRellich_relativeBound_linear_comb
-- name    : TeschlQM.KatoRellich.relativeBound_linear_comb
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T22:13:35.612369+00:00
-- url     : https://prove2.me/theorems/470d9745-e627-45b4-b2f7-1fc73e00acd3
-- title:
--   Lemma 6.1 — A bounded operators form a linear space
-- statement:
--   Let $A$, $B_1$, $B_2$ be linear operators in a complex Hilbert space $\mathfrak{H}$, and suppose $B_1$ and $B_2$ are $A$ bounded with $A$-bounds $a_1$ and $a_2$. Then for all $\alpha_1, \alpha_2 \in \mathbb{C}$ the operator $\alpha_1 B_1 + \alpha_2 B_2$, defined on $\mathfrak{D}(B_1) \cap \mathfrak{D}(B_2)$, is also $A$ bounded, and its $A$-bound satisfies
--   $$\text{$A$-bound of } (\alpha_1 B_1 + \alpha_2 B_2) \;\le\; |\alpha_1| a_1 + |\alpha_2| a_2.$$
--   In particular, the $A$ bounded operators form a linear space.
--
--   **Formalization Note.** The book writes "$A$-bound less than $|\alpha_1|a_1 + |\alpha_2|a_2$"; the bound can be attained (take $\alpha_1 = \alpha_2 = 0$), so the statement is "at most". $A$-bounds are compared in $[0, \infty]$. The sum and scalar multiples are Mathlib's operations on `LinearPMap` (the sum lives on the intersection of the domains).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 133, Lemma 6.1

import Mathlib
import Definitions.Def_TeschlQM_KatoRellich_IsRelativelyBounded

namespace TeschlQM.KatoRellich

open scoped ENNReal

/-- Teschl, Lemma 6.1, p. 133. If `B₁, B₂` are `A` bounded with `A`-bounds `a₁, a₂`, then
`α₁B₁ + α₂B₂` (on `𝔇(B₁) ∩ 𝔇(B₂)`) is `A` bounded with `A`-bound at most `|α₁|a₁ + |α₂|a₂`.
(The book writes "less than"; the bound is attained, e.g. for `α₁ = α₂ = 0`, so it means `≤`.) -/
theorem relativeBound_linear_comb {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B₁ B₂ : H →ₗ.[ℂ] H) (h₁ : IsRelativelyBounded A B₁) (h₂ : IsRelativelyBounded A B₂)
    (α₁ α₂ : ℂ) :
    IsRelativelyBounded A (α₁ • B₁ + α₂ • B₂) ∧
      relativeBound A (α₁ • B₁ + α₂ • B₂) ≤
        ENNReal.ofReal ‖α₁‖ * relativeBound A B₁ + ENNReal.ofReal ‖α₂‖ * relativeBound A B₂ := by sorry

end TeschlQM.KatoRellich
