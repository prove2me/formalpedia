-- Prove2me | Theorems.Thm_SustainableFashion_Variety_proposition_4_ii
-- name    : SustainableFashion.Variety.proposition_4_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:57.691054+00:00
-- url     : https://prove2.me/theorems/0b9970a1-b70f-4b95-8dc0-9fb06a5e2573
-- title:
--   Proposition 4(ii), p. 16 — optimal quality u* decreases in γ, increases in β, decreases in n̄
-- statement:
--   Fix admissible parameters $0<k<k'$, $\theta,\gamma,\beta,\bar n>0$, and consider problem (1), in which the firm jointly chooses the number of styles $m\ge1$, the quality $u\ge0$ and the per-style inventory $0\le q\le\bar n$ to maximise
--   $$\mathbb E\Pi=\Big(a+\theta u+\frac\gamma2-\frac{\gamma}{4m}\Big)\frac{\bar n}{2}-m\frac k2u^2q-\frac{k'}{2}u^2\frac{(\bar n-q)^2}{2\bar n}-\beta m .$$
--   Then problem (1) has an optimal solution, and the optimal product quality $u^*$
--
--   1. decreases in the fashion sensitivity $\gamma$,
--   2. increases in the design cost $\beta$ of a new style,
--   3. decreases in the market-size parameter $\bar n$,
--
--   where each comparison changes one parameter, keeps the others fixed, and compares the quality of **every** optimal solution before the change with that of **every** optimal solution after it.
--
--   This is the paper's headline: when variety is endogenous, quality falls as consumers become more fashion-sensitive, as new styles get cheaper to design, or as the market grows. For a fixed number of styles the optimal quality does not depend on $\gamma$, $\beta$ or $\bar n$ at all, so the effect runs entirely through the optimal variety.
--
--   **Formalization Note** "Increases/decreases" are weak (in the paper's Region I the optimal quality is constant); the parameter changes are strict. The number of styles is a real number $m\ge1$, as in the paper's analysis. The existence conjunct rules out a vacuous reading.
-- source:
--   Long & Nasiry, Sustainability in the Fast Fashion Industry, SSRN 3486502 author's manuscript (2021; MSOM doi:10.1287/msom.2021.1054), Proposition 4(ii), p. 16 (proof p. 42)

import Mathlib
import Definitions.Def_SustainableFashion_Variety_Setting

namespace SustainableFashion.Variety

theorem proposition_4_ii (P : Params) (hP : P.Admissible) :
    (∃ m u q, IsOptimal P m u q) ∧
    (∀ γ₂, P.γ < γ₂ → ∀ m₁ u₁ q₁ m₂ u₂ q₂,
        IsOptimal P m₁ u₁ q₁ → IsOptimal { P with γ := γ₂ } m₂ u₂ q₂ → u₂ ≤ u₁) ∧
    (∀ β₂, P.β < β₂ → ∀ m₁ u₁ q₁ m₂ u₂ q₂,
        IsOptimal P m₁ u₁ q₁ → IsOptimal { P with β := β₂ } m₂ u₂ q₂ → u₁ ≤ u₂) ∧
    (∀ n₂, P.nbar < n₂ → ∀ m₁ u₁ q₁ m₂ u₂ q₂,
        IsOptimal P m₁ u₁ q₁ → IsOptimal { P with nbar := n₂ } m₂ u₂ q₂ → u₂ ≤ u₁) := by sorry

end SustainableFashion.Variety
