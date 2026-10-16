-- Prove2me | Theorems.Thm_QuantumEcon_Duopoly_lemma_1
-- name    : QuantumEcon.Duopoly.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:41:45.112521+00:00
-- url     : https://prove2.me/theorems/9a6a429f-921d-4013-af4a-6125f2dd612e
-- title:
--   Lemma 1: positive investments and strict concavity under explicit thresholds
-- statement:
--   Assume the model’s standing conditions, $a>a^*$, and $B_i>\max\{\widehat B_i,\widehat{\widehat B}_i\}$ for both firms, using the thresholds derived in the proof. Then both closed-form investments are strictly positive and each profit after substituting (3)–(4) is strictly concave in its own investment. This is the exact sufficient condition supplied by the proof of Lemma 1.
--
--   This statement is a source-indexed target for the two-stage model.
-- source:
--   Bova, Goldfarb, Melko, Quantum Economic Advantage, NBER Working Paper No. 29724 (February 2022), PDF p. 26, Lemma 1 conclusion; PDF p. 11, Lemma 1

import Definitions.Def_QuantumEcon_Duopoly_Setting

set_option autoImplicit false

namespace QuantumEcon.Duopoly

/-- Bova, Goldfarb, Melko, Quantum Economic Advantage, NBER Working Paper No. 29724
(February 2022), PDF p. 11, Lemma 1, in the exact sufficient form concluded on PDF p. 26.
Formalization Note: `Lemma1Cond` uses strict maximum thresholds; strict concavity is
for the algebraic reduced profits with (3)–(4) substituted. -/
theorem lemma_1 (P : Params) (hP : Standing P) (hL : Lemma1Cond P) :
    0 < xStar₁ P ∧ 0 < xStar₂ P ∧
    (∀ x₂ : ℝ, StrictConcaveOn ℝ Set.univ
      (fun y => profit₁ P y (qStar₁ P y x₂) (qStar₂ P y x₂))) ∧
    (∀ x₁ : ℝ, StrictConcaveOn ℝ Set.univ
      (fun y => profit₂ P y (qStar₁ P x₁ y) (qStar₂ P x₁ y))) := by sorry

end QuantumEcon.Duopoly
