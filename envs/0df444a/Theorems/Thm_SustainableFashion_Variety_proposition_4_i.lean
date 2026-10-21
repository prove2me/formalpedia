-- Prove2me | Theorems.Thm_SustainableFashion_Variety_proposition_4_i
-- name    : SustainableFashion.Variety.proposition_4_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:44.26216+00:00
-- url     : https://prove2.me/theorems/934bb3f1-5979-46cc-8867-034b4562efaa
-- title:
--   Proposition 4(i), p. 16 — m* increases in γ, decreases in β, decreases in k′, increases in n̄
-- statement:
--   Fix admissible parameters. Problem (1) has an optimal solution, and the optimal number of styles $m^*$ responds to the parameters as follows (each comparison changes one parameter, keeps the others fixed, and compares **every** optimal solution before the change with **every** optimal solution after it):
--
--   1. $m^*$ increases in the fashion sensitivity $\gamma$;
--   2. $m^*$ decreases in the design cost $\beta$;
--   3. $m^*$ decreases in the quick-response cost coefficient $k'$;
--   4. $m^*$ increases in the market-size parameter $\bar n$.
--
--   **Formalization Note** "Increases/decreases" are weak; the parameter changes are strict (with equal parameters the claim would say all optima share one $m$, which fails at the thresholds of Proposition 3). The existence of an optimum is part of the statement so that the monotonicity is not vacuous.
-- source:
--   Long & Nasiry, Sustainability in the Fast Fashion Industry, SSRN 3486502 author's manuscript (2021; MSOM doi:10.1287/msom.2021.1054), Proposition 4(i), p. 16 (proof p. 42)

import Mathlib
import Definitions.Def_SustainableFashion_Variety_Setting

namespace SustainableFashion.Variety

theorem proposition_4_i (P : Params) (hP : P.Admissible) :
    (∃ m u q, IsOptimal P m u q) ∧
    (∀ γ₂, P.γ < γ₂ → ∀ m₁ u₁ q₁ m₂ u₂ q₂,
        IsOptimal P m₁ u₁ q₁ → IsOptimal { P with γ := γ₂ } m₂ u₂ q₂ → m₁ ≤ m₂) ∧
    (∀ β₂, P.β < β₂ → ∀ m₁ u₁ q₁ m₂ u₂ q₂,
        IsOptimal P m₁ u₁ q₁ → IsOptimal { P with β := β₂ } m₂ u₂ q₂ → m₂ ≤ m₁) ∧
    (∀ k₂', P.k' < k₂' → ∀ m₁ u₁ q₁ m₂ u₂ q₂,
        IsOptimal P m₁ u₁ q₁ → IsOptimal { P with k' := k₂' } m₂ u₂ q₂ → m₂ ≤ m₁) ∧
    (∀ n₂, P.nbar < n₂ → ∀ m₁ u₁ q₁ m₂ u₂ q₂,
        IsOptimal P m₁ u₁ q₁ → IsOptimal { P with nbar := n₂ } m₂ u₂ q₂ → m₁ ≤ m₂) := by sorry

end SustainableFashion.Variety
