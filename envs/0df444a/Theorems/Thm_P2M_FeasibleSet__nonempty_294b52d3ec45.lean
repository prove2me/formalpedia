-- Prove2me | Theorems.Thm_P2M_FeasibleSet__nonempty_294b52d3ec45
-- name    : P2M_FeasibleSet__nonempty_294b52d3ec45
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:11:13.499243+00:00
-- url     : https://prove2.me/theorems/15810cba-9424-4f58-8dc4-a462dc983ab2
-- title:
--   P2 M Feasible Set  nonempty 294b52d3ec45: P2 M Feasible Set  nonempty 294b52d3ec45
-- statement:
--   The product of the conditional marginals witnesses nonemptiness of
--       the one-step feasible set, for probability kernels.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/FeasNonempty.lean#L66-L76
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/FeasNonempty.lean#L66-L76

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
omit [MeasurableSpace X₀] [MeasurableSpace Y₀]

theorem P2M_FeasibleSet__nonempty_294b52d3ec45
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (hκμ : ∀ x, IsProbabilityMeasure (κ_μ x))
    (hκν : ∀ y, IsProbabilityMeasure (κ_ν y))
    (z₀ : X₀ × Y₀) :
    (FeasibleSet₀ κ_μ κ_ν z₀).Nonempty := by sorry

alias «FeasibleSet₀».«nonempty» := P2M_FeasibleSet__nonempty_294b52d3ec45
