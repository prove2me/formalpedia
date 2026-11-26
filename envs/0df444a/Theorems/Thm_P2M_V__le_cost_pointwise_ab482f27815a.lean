-- Prove2me | Theorems.Thm_P2M_V__le_cost_pointwise_ab482f27815a
-- name    : P2M_V__le_cost_pointwise_ab482f27815a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T07:59:11.642432+00:00
-- url     : https://prove2.me/theorems/05d6994d-d3a8-4e5c-8d92-51834031965d
-- title:
--   P2 M V  le cost pointwise ab482f27815a: P2 M V  le cost pointwise ab482f27815a
-- statement:
--   The P2 M V  le cost pointwise ab482f27815a construction uses the P2 M V  le cost pointwise ab482f27815a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LowerBound.lean#L16-L21
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LowerBound.lean#L16-L21

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_LowerBound
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
variable (c₀ : X₀ × Y₀ → ENNReal) (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)
set_option linter.unusedSectionVars false

theorem P2M_V__le_cost_pointwise_ab482f27815a
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (z₀ : X₀ × Y₀) (γ : Measure (X₁ × Y₁))
    (hγ : γ ∈ FeasibleSet₀ κ_μ κ_ν z₀) :
    V₀ c₀ c₁ κ_μ κ_ν z₀ ≤ c₀ z₀ + ∫⁻ z₁, c₁ (z₀, z₁) ∂γ := by sorry

alias «V₀_le_cost_pointwise» := P2M_V__le_cost_pointwise_ab482f27815a
