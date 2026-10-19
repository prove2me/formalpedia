-- Prove2me | Theorems.Thm_SustainableFashion_Variety_proposition_2_iii
-- name    : SustainableFashion.Variety.proposition_2_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:33.163985+00:00
-- url     : https://prove2.me/theorems/862af7ae-1aa1-41eb-b924-f37afd523a3b
-- title:
--   Proposition 2(iii), p. 15 — for given m, the optimal quality û decreases in k′ and m
-- statement:
--   Fix parameters with $0<k<k'$, $\theta>0$ and $\bar n>0$. For a given number of styles $m\ge1$, let $\hat u$ denote the quality component of any maximiser of the expected profit (1) over $u\ge0$, $0\le q\le\bar n$. Then:
--
--   1. $\hat u$ is (weakly) decreasing in $m$: if $1\le m_1\le m_2$, every optimal quality at $m_2$ is at most every optimal quality at $m_1$;
--   2. $\hat u$ is (weakly) decreasing in $k'$: if $k'<k_2'$ and all other parameters are kept fixed, every optimal quality under $k_2'$ is at most every optimal quality under $k'$.
--
--   This is the link between variety and quality: more styles mean more leftovers or more quick response, and the firm lowers quality to cut the unit cost.
--
--   **Formalization Note** "Decreases" is read weakly: $\hat u=\theta/k'$ is constant in $m$ for $m>k'/k$. The comparison in $k'$ changes only the coordinate $k'$ of the parameter vector.
-- source:
--   Long & Nasiry, Sustainability in the Fast Fashion Industry, SSRN 3486502 author's manuscript (2021; MSOM doi:10.1287/msom.2021.1054), Proposition 2(iii), p. 15 (proof p. 39)

import Mathlib
import Definitions.Def_SustainableFashion_Variety_Setting

namespace SustainableFashion.Variety

theorem proposition_2_iii (P : Params)
    (hk : 0 < P.k) (hkk' : P.k < P.k') (hθ : 0 < P.θ) (hn : 0 < P.nbar) :
    (∀ m₁ m₂ u₁ q₁ u₂ q₂ : ℝ, 1 ≤ m₁ → m₁ ≤ m₂ →
        IsOptimalGiven P m₁ u₁ q₁ → IsOptimalGiven P m₂ u₂ q₂ → u₂ ≤ u₁) ∧
    (∀ k₂' : ℝ, P.k' < k₂' → ∀ m u₁ q₁ u₂ q₂ : ℝ, 1 ≤ m →
        IsOptimalGiven P m u₁ q₁ → IsOptimalGiven { P with k' := k₂' } m u₂ q₂ → u₂ ≤ u₁) := by sorry

end SustainableFashion.Variety
