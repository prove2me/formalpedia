-- Prove2me | Theorems.Thm_QuantumEcon_Duopoly_eq14_15_second_order
-- name    : QuantumEcon.Duopoly.eq14_15_second_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:41:56.7689+00:00
-- url     : https://prove2.me/theorems/a03f0675-846f-48a4-999b-42fc6022f1c1
-- title:
--   (14)–(15): second derivatives of reduced profits
-- statement:
--   Under the standing model assumptions, substitute the first-order quantities (3)–(4) into each firm’s profit. The second derivative in the firm’s own investment is $(8-B_i(-4+\gamma^2)^2)/(-4+\gamma^2)^2$ for $i=1,2$. These formulas set the curvature thresholds in Lemma 1.
--
--   This statement is a source-indexed target for the two-stage model.
-- source:
--   Bova, Goldfarb, Melko, Quantum Economic Advantage, NBER Working Paper No. 29724 (February 2022), PDF p. 24, (14)–(15)

import Definitions.Def_QuantumEcon_Duopoly_Setting

set_option autoImplicit false

namespace QuantumEcon.Duopoly

/-- Bova, Goldfarb, Melko, Quantum Economic Advantage, NBER Working Paper No. 29724
(February 2022), PDF p. 24, (14)–(15). Formalization Note: derivatives are of the
algebraic reduced profits obtained by substituting (3)–(4), over real investments;
`Standing` carries the model assumptions under which the formulas are stated. -/
theorem eq14_15_second_order (P : Params) (hP : Standing P)
    (x₁ x₂ : ℝ) :
    deriv (deriv (fun y => profit₁ P y (qStar₁ P y x₂) (qStar₂ P y x₂))) x₁ =
      (8 - P.B₁ * (-4 + P.γ ^ 2) ^ 2) / (-4 + P.γ ^ 2) ^ 2 ∧
    deriv (deriv (fun y => profit₂ P y (qStar₁ P x₁ y) (qStar₂ P x₁ y))) x₂ =
      (8 - P.B₂ * (-4 + P.γ ^ 2) ^ 2) / (-4 + P.γ ^ 2) ^ 2 := by sorry

end QuantumEcon.Duopoly
