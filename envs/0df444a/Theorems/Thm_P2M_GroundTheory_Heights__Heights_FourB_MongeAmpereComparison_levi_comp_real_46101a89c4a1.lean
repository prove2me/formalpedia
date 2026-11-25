-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_levi_comp_real_46101a89c4a1
-- name    : P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_levi_comp_real_46101a89c4a1
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:35:22.876661+00:00
-- url     : https://prove2.me/theorems/80b3b036-fb45-46fd-8974-e49033ceafdb
-- title:
--   P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison levi comp real 46101a89c4a1: P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison levi comp real 46101a89c4a1
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison levi comp real 46101a89c4a1 construction uses the P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison levi comp real 46101a89c4a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PMongeAmpereComparison.lean#L54-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PMongeAmpereComparison.lean#L54-L75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PMongeAmpereComparison
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison

theorem P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_levi_comp_real_46101a89c4a1 {ι : Type*} [Fintype ι] {ρ ρ' : ℝ → ℝ} {ρ'' : ℝ} {t : (ι → ℂ) → ℝ}
    {z : ι → ℂ} (hρ : ∀ u, HasDerivAt ρ (ρ' u) u) (hρ' : HasDerivAt ρ' ρ'' (t z))
    (ht : ContDiffAt ℝ 2 t z) (w : ι → ℂ) :
    levi (ρ ∘ t) z w = ρ' (t z) * levi t z w +
      ρ'' * ((fderiv ℝ t z w) ^ 2 + (fderiv ℝ t z (Complex.I • w)) ^ 2) / 4 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«MongeAmpereComparison».«levi_comp_real» := P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_levi_comp_real_46101a89c4a1
