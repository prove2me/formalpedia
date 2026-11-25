-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLogPow_hessC_log_comp_d38474af266b
-- name    : P2M_GroundTheory_Heights__Heights_MaDensLogPow_hessC_log_comp_d38474af266b
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:49:25.855257+00:00
-- url     : https://prove2.me/theorems/32937354-fa56-4e14-9f45-19373ad9dcc4
-- title:
--   P2 M Ground Theory Heights  Heights Ma Dens Log Pow hess C log comp d38474af266b: P2 M Ground Theory Heights  Heights Ma Dens Log Pow hess C log comp d38474af266b
-- statement:
--   The P2 M Ground Theory Heights  Heights Ma Dens Log Pow hess C log comp d38474af266b construction uses the P2 M Ground Theory Heights  Heights Ma Dens Log Pow hess C log comp d38474af266b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLogPow.lean#L131-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLogPow.lean#L131-L166

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaDensLogPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLogPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.MaDensLogPow
variable {D : ℕ}

theorem P2M_GroundTheory_Heights__Heights_MaDensLogPow_hessC_log_comp_d38474af266b {p : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (hp : ContDiffAt ℝ 2 p y) (hpos : 0 < p y) :
    hessC (Real.log ∘ p) y =
      (((p y)⁻¹ : ℝ) : ℂ) • hessC p y + ((-((p y) ^ 2)⁻¹ : ℝ) : ℂ) • gradMat p p y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MaDensLogPow».«hessC_log_comp» := P2M_GroundTheory_Heights__Heights_MaDensLogPow_hessC_log_comp_d38474af266b
