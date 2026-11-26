-- Prove2me | Theorems.Thm_P2M_bellman_value_eq__629ebbd0a78b
-- name    : P2M_bellman_value_eq__629ebbd0a78b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:15:17.274744+00:00
-- url     : https://prove2.me/theorems/8f3611f9-f97f-4c19-b732-0269d9506aa2
-- title:
--   P2 M bellman value eq  629ebbd0a78b: P2 M bellman value eq  629ebbd0a78b
-- statement:
--   **T=1 Bellman value representation, probability-kernel form.**
--       `bellman_value_eq` with both side conditions discharged: the
--       nonemptiness hypothesis `h_Gamma_ne` follows from the kernels being
--       probability-valued (`FeasibleSet₀.nonempty`), and the mass bound
--       `h_prob` from the probability marginals (`CouplingSet₀.measure_univ`).
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/FeasNonempty.lean#L97-L111
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/FeasNonempty.lean#L97-L111

import Definitions.Def_BicausalOT_MultiPeriod
import Definitions.Def_BicausalOT_ValueRepresentation
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_BicausalOT_FeasNonempty
set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
variable (c₀ : X₀ × Y₀ → ENNReal) (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)

theorem P2M_bellman_value_eq__629ebbd0a78b
    (μ₀ : Measure X₀) [IsProbabilityMeasure μ₀]
    (ν₀ : Measure Y₀) [IsProbabilityMeasure ν₀]
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (hκμ : ∀ x, IsProbabilityMeasure (κ_μ x))
    (hκν : ∀ y, IsProbabilityMeasure (κ_ν y)) :
    ⨅ (γ₀ : Measure (X₀ × Y₀)) (γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁))
        (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀)
        (_ : ∀ z₀, γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀),
        totalCost c₀ c₁ γ₀ γ₁
    = ⨅ (γ₀ : Measure (X₀ × Y₀)) (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀),
        ∫⁻ z₀, V₀ c₀ c₁ κ_μ κ_ν z₀ ∂γ₀ := by sorry

alias «bellman_value_eq'» := P2M_bellman_value_eq__629ebbd0a78b
