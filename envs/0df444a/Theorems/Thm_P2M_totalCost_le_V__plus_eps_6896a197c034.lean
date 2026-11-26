-- Prove2me | Theorems.Thm_P2M_totalCost_le_V__plus_eps_6896a197c034
-- name    : P2M_totalCost_le_V__plus_eps_6896a197c034
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T07:59:32.963492+00:00
-- url     : https://prove2.me/theorems/3f34141d-7b9f-58dd-b3dd-0cb2c983ee31
-- title:
--   P2 M total Cost le V  plus eps 6896a197c034: P2 M total Cost le V  plus eps 6896a197c034
-- statement:
--   The P2 M total Cost le V  plus eps 6896a197c034 construction uses the P2 M total Cost le V  plus eps 6896a197c034 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/UpperBound.lean#L44-L65
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/UpperBound.lean#L44-L65

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_DescriptiveSetTheory_JankovVonNeumann
import Definitions.Def_BicausalOT_UpperBound
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
variable (c₀ : X₀ × Y₀ → ENNReal) (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)

theorem P2M_totalCost_le_V__plus_eps_6896a197c034
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (γ₀ : Measure (X₀ × Y₀))
    (γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁))
    (ε : ENNReal)
    (h_opt : ∀ z₀, ∫⁻ z₁, c₁ (z₀, z₁) ∂(γ₁ z₀)
      ≤ (⨅ (m : Measure (X₁ × Y₁)) (_ : m ∈ FeasibleSet₀ κ_μ κ_ν z₀),
          ∫⁻ z₁, c₁ (z₀, z₁) ∂m) + ε) :
    totalCost c₀ c₁ γ₀ γ₁
    ≤ ∫⁻ z₀, (V₀ c₀ c₁ κ_μ κ_ν z₀ + ε) ∂γ₀ := by sorry

alias «totalCost_le_V₀_plus_eps» := P2M_totalCost_le_V__plus_eps_6896a197c034
