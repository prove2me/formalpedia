-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_cca_differentiableOn_fderiv_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.cca_differentiableOn_fderiv_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:44:19.361996+00:00
-- url     : https://prove2.me/theorems/9329f8e4-07df-5874-8e40-3bb380d9b677
-- title:
--   S7: cca differentiable On fderiv apply
-- statement:
--   The S7 construction uses the cca differentiable On fderiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasChainA.lean#L149-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasChainA.lean#L149-L159

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric Set Filter Topology MeasureTheory Complex
open scoped ContDiff Real
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem ReciprocityTheory.ChartRestriction.DS.S7.cca_differentiableOn_fderiv_apply [FiniteDimensional ℂ X] [CompleteSpace E] {F : X → E}
    {U : Set X} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (u : X) :
    DifferentiableOn ℂ (fun z => fderiv ℂ F z u) U := by sorry
