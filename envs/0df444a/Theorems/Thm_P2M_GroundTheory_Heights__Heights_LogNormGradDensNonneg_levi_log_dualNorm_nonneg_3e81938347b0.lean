-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogNormGradDensNonneg_levi_log_dualNorm_nonneg_3e81938347b0
-- name    : P2M_GroundTheory_Heights__Heights_LogNormGradDensNonneg_levi_log_dualNorm_nonneg_3e81938347b0
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:28:49.339307+00:00
-- url     : https://prove2.me/theorems/4696de40-835e-4e46-9c06-a2573575f370
-- title:
--   P2 M Ground Theory Heights  Heights Log Norm Grad Dens Nonneg levi log dual Norm nonneg 3e81938347b0: P2 M Ground Theory Heights  Heights Log Norm Grad Dens Nonneg levi log dual Norm nonneg 3e81938347
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Norm Grad Dens Nonneg levi log dual Norm nonneg 3e81938347b0 construction uses the P2 M Ground Theory Heights  Heights Log Norm Grad Dens Nonneg levi log dual Norm nonneg 3e81938347b0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLogNormGradDensNonneg.lean#L24-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLogNormGradDensNonneg.lean#L24-L48

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

theorem P2M_GroundTheory_Heights__Heights_LogNormGradDensNonneg_levi_log_dualNorm_nonneg_3e81938347b0 {n : ℕ} (h : HermNorm n) {x : Fin n → ℂ} (hx : x ≠ 0)
    (w : Fin n → ℂ) : 0 ≤ levi (fun x => Real.log (h.dualNorm x)) x w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogNormGradDensNonneg».«levi_log_dualNorm_nonneg» := P2M_GroundTheory_Heights__Heights_LogNormGradDensNonneg_levi_log_dualNorm_nonneg_3e81938347b0
