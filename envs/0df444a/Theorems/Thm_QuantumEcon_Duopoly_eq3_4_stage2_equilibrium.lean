-- Prove2me | Theorems.Thm_QuantumEcon_Duopoly_eq3_4_stage2_equilibrium
-- name    : QuantumEcon.Duopoly.eq3_4_stage2_equilibrium
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T09:41:44.9946+00:00
-- url     : https://prove2.me/theorems/57e6bb2a-b4db-46ad-91bb-da4de42ac6a6
-- title:
--   (3)–(4): nonnegative interior Cournot quantities are the unique stage-2 equilibrium
-- statement:
--   Under the standing model assumptions, for nonnegative investments $x_1,x_2$, suppose both first-order quantities in (3)–(4) are nonnegative. Then a quantity pair is a stage-2 Cournot equilibrium exactly when it equals those two quantities. This identifies the paper’s interior formula with the constrained quantity game.
--
--   This statement is a source-indexed target for the two-stage model.
-- source:
--   Bova, Goldfarb, Melko, Quantum Economic Advantage, NBER Working Paper No. 29724 (February 2022), PDF p. 11, (3)–(4)

import Definitions.Def_QuantumEcon_Duopoly_Setting

set_option autoImplicit false

namespace QuantumEcon.Duopoly

/-- Bova, Goldfarb, Melko, Quantum Economic Advantage, NBER Working Paper No. 29724
(February 2022), PDF p. 11, (3)–(4). Formalization Note: the printed first-order
quantities describe the constrained Cournot equilibrium when both are nonnegative.
The standing model assumptions and nonnegative investment domain are explicit. -/
theorem eq3_4_stage2_equilibrium (P : Params) (hP : Standing P)
    (x₁ x₂ q₁ q₂ : ℝ) (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂)
    (hq₁ : 0 ≤ qStar₁ P x₁ x₂) (hq₂ : 0 ≤ qStar₂ P x₁ x₂) :
    IsStage2Nash P x₁ x₂ q₁ q₂ ↔
      q₁ = qStar₁ P x₁ x₂ ∧ q₂ = qStar₂ P x₁ x₂ := by sorry

end QuantumEcon.Duopoly
