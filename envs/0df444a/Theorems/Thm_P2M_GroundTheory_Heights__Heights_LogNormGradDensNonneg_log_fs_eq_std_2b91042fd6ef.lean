-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogNormGradDensNonneg_log_fs_eq_std_2b91042fd6ef
-- name    : P2M_GroundTheory_Heights__Heights_LogNormGradDensNonneg_log_fs_eq_std_2b91042fd6ef
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:28:47.911006+00:00
-- url     : https://prove2.me/theorems/7c1fc9e6-b9a6-4c7d-9e93-d2c94aa2993a
-- title:
--   P2 M Ground Theory Heights  Heights Log Norm Grad Dens Nonneg log fs eq std 2b91042fd6ef: P2 M Ground Theory Heights  Heights Log Norm Grad Dens Nonneg log fs eq std 2b91042fd6ef
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Norm Grad Dens Nonneg log fs eq std 2b91042fd6ef construction uses the P2 M Ground Theory Heights  Heights Log Norm Grad Dens Nonneg log fs eq std 2b91042fd6ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLogNormGradDensNonneg.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLogNormGradDensNonneg.lean#L18-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogNormGradDensNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLogNormGradDensNonneg
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
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.LogNormGradDensNonneg

theorem P2M_GroundTheory_Heights__Heights_LogNormGradDensNonneg_log_fs_eq_std_2b91042fd6ef (n : ℕ) :
    (fun z : Fin n → ℂ => Real.log ((ReciprocityTheory.ChartRestriction.G.Geo.fsMetric (Fin n)).ρ z)) =
      fun z => Real.log ((HermNorm.std n).dualNorm z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogNormGradDensNonneg».«log_fs_eq_std» := P2M_GroundTheory_Heights__Heights_LogNormGradDensNonneg_log_fs_eq_std_2b91042fd6ef
