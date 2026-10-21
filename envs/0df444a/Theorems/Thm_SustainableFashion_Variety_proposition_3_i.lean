-- Prove2me | Theorems.Thm_SustainableFashion_Variety_proposition_3_i
-- name    : SustainableFashion.Variety.proposition_3_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:36.660184+00:00
-- url     : https://prove2.me/theorems/7a2bd3ca-94cb-49b9-baa1-8288d9ca1da6
-- title:
--   Proposition 3(i), p. 15 — if γ ≤ 2(k′ − k)²θ²/(kk′(2k′ − k)) then m* = 1
-- statement:
--   Fix admissible parameters with
--   $$\gamma\le\frac{2(k'-k)^2\theta^2}{kk'(2k'-k)} .$$
--   Then problem (1) has an optimal solution with a single style, and every optimal solution $(m^*,u^*,q^*)$ of problem (1) has $m^*=1$.
--
--   When consumers care little about fashion, the extra production cost of variety is never worth paying.
--
--   **Formalization Note** "$m^*=1$" is read as: an optimum with $m=1$ exists and every optimum has $m=1$.
-- source:
--   Long & Nasiry, Sustainability in the Fast Fashion Industry, SSRN 3486502 author's manuscript (2021; MSOM doi:10.1287/msom.2021.1054), Proposition 3(i), p. 15 (proof pp. 39–42)

import Mathlib
import Definitions.Def_SustainableFashion_Variety_Setting

namespace SustainableFashion.Variety

theorem proposition_3_i (P : Params) (hP : P.Admissible)
    (hγ : P.γ ≤ 2 * (P.k' - P.k) ^ 2 * P.θ ^ 2 / (P.k * P.k' * (2 * P.k' - P.k))) :
    (∃ u q, IsOptimal P 1 u q) ∧ ∀ m u q, IsOptimal P m u q → m = 1 := by sorry

end SustainableFashion.Variety
