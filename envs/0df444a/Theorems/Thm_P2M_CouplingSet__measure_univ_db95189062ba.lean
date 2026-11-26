-- Prove2me | Theorems.Thm_P2M_CouplingSet__measure_univ_db95189062ba
-- name    : P2M_CouplingSet__measure_univ_db95189062ba
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:11:10.848502+00:00
-- url     : https://prove2.me/theorems/6badb313-f7c0-5911-aad6-a37aceac1488
-- title:
--   P2 M Coupling Set  measure univ db95189062ba: P2 M Coupling Set  measure univ db95189062ba
-- statement:
--   Any coupling of probability marginals has total mass one.  Makes the
--       hypothesis `h_prob` of `bellman_value_leq` / `bellman_value_eq`
--       redundant.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/FeasNonempty.lean#L81-L88
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/FeasNonempty.lean#L81-L88

import Definitions.Def_BicausalOT_MultiPeriod
import Definitions.Def_BicausalOT_ValueRepresentation
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_BicausalOT_FeasNonempty
import Theorems.Thm_MultiPeriod_Feas_measure_univ

set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]

theorem P2M_CouplingSet__measure_univ_db95189062ba
    {μ₀ : Measure X₀} {ν₀ : Measure Y₀} [hμ₀ : IsProbabilityMeasure μ₀]
    {γ₀ : Measure (X₀ × Y₀)} (hγ₀ : γ₀ ∈ CouplingSet₀ μ₀ ν₀) :
    γ₀ Set.univ = 1 := by sorry

alias «CouplingSet₀».«measure_univ» := P2M_CouplingSet__measure_univ_db95189062ba
