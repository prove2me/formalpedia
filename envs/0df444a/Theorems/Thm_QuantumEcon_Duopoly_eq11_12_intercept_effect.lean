-- Prove2me | Theorems.Thm_QuantumEcon_Duopoly_eq11_12_intercept_effect
-- name    : QuantumEcon.Duopoly.eq11_12_intercept_effect
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T09:42:07.70562+00:00
-- url     : https://prove2.me/theorems/76586acc-14c5-4166-8eb0-40f37b4bb22e
-- title:
--   (11)–(12): demand intercept raises quantum profit more
-- statement:
--   In the no-investment model, assume both interior Cournot quantities are positive. The derivatives of the two closed-form optimal profits with respect to the common intercept $a$ are the displayed expressions following (11)–(12), and satisfy $0<\partial_a\pi_2^*<\partial_a\pi_1^*$. This compares the firms’ gains from a larger market.
--
--   This statement is a source-indexed target for the two-stage model.
-- source:
--   Bova, Goldfarb, Melko, Quantum Economic Advantage, NBER Working Paper No. 29724 (February 2022), PDF p. 15, comparative static following (11)–(12)

import Definitions.Def_QuantumEcon_Duopoly_Setting

set_option autoImplicit false

namespace QuantumEcon.Duopoly

/-- Bova, Goldfarb, Melko, Quantum Economic Advantage, NBER Working Paper No. 29724
(February 2022), PDF p. 15, comparative static following (11)–(12).
Formalization Note: these are the no-investment profit formulas; positive interior
quantities are explicit hypotheses. -/
theorem eq11_12_intercept_effect (a c γ : ℝ)
    (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) (hc₁ : 1 < c) (hcc : c < c ^ 2)
    (hca : c ^ 2 < a)
    (hq₁ : 0 < (a * (-2 + γ) + c * (2 - c * γ)) / (-4 + γ ^ 2))
    (hq₂ : 0 < (c * (2 * c - γ) + a * (-2 + γ)) / (-4 + γ ^ 2)) :
    let π₁ : ℝ → ℝ := fun z =>
      (z * (-2 + γ) + c * (2 - c * γ)) ^ 2 / (-4 + γ ^ 2) ^ 2
    let π₂ : ℝ → ℝ := fun z =>
      (c * (2 * c - γ) + z * (-2 + γ)) ^ 2 / (-4 + γ ^ 2) ^ 2
    HasDerivAt π₁
      (2 * (-2 + γ) * (a * (-2 + γ) + c * (2 - c * γ)) /
        (-4 + γ ^ 2) ^ 2) a ∧
    HasDerivAt π₂
      (2 * (c * (2 * c - γ) + a * (-2 + γ)) * (-2 + γ) /
        (-4 + γ ^ 2) ^ 2) a ∧
    0 < deriv π₂ a ∧ deriv π₂ a < deriv π₁ a := by sorry

end QuantumEcon.Duopoly
