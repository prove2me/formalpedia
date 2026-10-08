-- Prove2me | Theorems.Thm_SpenglerVertical_DoubleMarginalization_price_rises_with_cost
-- name    : SpenglerVertical.DoubleMarginalization.price_rises_with_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:04.088408+00:00
-- url     : https://prove2.me/theorems/685d2abe-e286-404e-982e-aa7f0bd72eba
-- title:
--   Section III — an increment in cost (a monopolistic surcharge or otherwise) lowers output and raises the profit-maximizing price
-- statement:
--   Let $D$ be a demand curve and $c_1<c_2$ two constant unit costs. Let $p_1$ be a profit-maximizing price at cost $c_1$ and $p_2$ one at cost $c_2$. Then
--
--   1. output does not rise with cost: $D(p_2)\le D(p_1)$;
--   2. if $D$ is non-increasing and $D(p_2)>0$, the price does not fall: $p_1\le p_2$;
--   3. if moreover $D$ is differentiable at $p_2$, the price rises strictly:
--   $$p_1<p_2.$$
--
--   Spengler states that every increment in cost, whatever its origin — in particular a "monopolistic" surcharge levied in earlier stages — is accompanied by a higher profit-maximizing price, so that a vertically integrated firm which escapes the surcharge lowers its price, and the greater the surcharge the greater the reduction (apply the result to two surcharges). This is the comparative-statics step on which the main theorem rests.
--
--   **Formalization Note** The paper's sentence also asserts a "relatively greater increment in the elasticity"; that part is made exact only for straight-line demand, in the footnote 6 milestone. No concavity, continuity or uniqueness of maximizers is assumed. Without differentiability the strict claim fails (a kinked demand curve can have the same maximizer at two costs).
-- source:
--   Spengler, Vertical integration and antitrust policy, J. Polit. Econ. 58 (1950), p. 350, Section III; https://doi.org/10.1086/256964

import Mathlib
import Definitions.Def_SpenglerVertical_DoubleMarginalization_Model

namespace SpenglerVertical.DoubleMarginalization

theorem price_rises_with_cost (D : ℝ → ℝ) (c₁ c₂ p₁ p₂ : ℝ) (hc : c₁ < c₂)
    (h₁ : IsProfitMax D c₁ p₁) (h₂ : IsProfitMax D c₂ p₂) :
    D p₂ ≤ D p₁ ∧
    (Antitone D → 0 < D p₂ → p₁ ≤ p₂) ∧
    (Antitone D → 0 < D p₂ → DifferentiableAt ℝ D p₂ → p₁ < p₂) := by sorry

end SpenglerVertical.DoubleMarginalization
