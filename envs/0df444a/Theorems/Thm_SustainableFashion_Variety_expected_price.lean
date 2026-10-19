-- Prove2me | Theorems.Thm_SustainableFashion_Variety_expected_price
-- name    : SustainableFashion.Variety.expected_price
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:34.151973+00:00
-- url     : https://prove2.me/theorems/040afe73-8048-4c07-bff0-a4d80dab0e4a
-- title:
--   §3.2, p. 11 — with m equally spaced styles, E|t* − x| = 1/(4m) and E[p] = a + θu + γ/2 − γ/(4m)
-- statement:
--   Let $m\ge1$ styles be equally spaced on the circle of unit circumference and let the trend $x$ be uniform on the circle. Then the expected arc distance from the trend to the nearest style is $1/(4m)$, and the expected price $p=a+\theta u+\gamma/2-\gamma|t^*-x|$ is
--   $$\mathbb E[p]=a+\theta u+\frac\gamma2-\frac{\gamma}{4m}$$
--   for all real $a,\theta,\gamma,u$.
--
--   This is the first term of problem (1): together with Lemma 1 it turns the location choice into a choice of the number $m$ of styles, with an expected price that increases in $m$.
--
--   **Formalization Note** Expectations are integrals over `AddCircle (1 : ℝ)` with its probability Haar measure; $m$ is a natural number here (the number of products placed on the circle).
-- source:
--   Long & Nasiry, Sustainability in the Fast Fashion Industry, SSRN 3486502 author's manuscript (2021; MSOM doi:10.1287/msom.2021.1054), §3.2, display preceding (1) ("By Lemma 1, given that the firm introduces m products …"), p. 11

import Mathlib
import Definitions.Def_SustainableFashion_Variety_Setting

namespace SustainableFashion.Variety

theorem expected_price (m : ℕ) [NeZero m] (a θ γ u : ℝ) :
    expNearestDist (equalSpacing m) = 1 / (4 * m) ∧
    ∫ x, (a + θ * u + γ / 2 - γ * nearestDist (equalSpacing m) x) =
      a + θ * u + γ / 2 - γ / (4 * m) := by sorry

end SustainableFashion.Variety
