-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradDensSheetBound_hessC_pm_posSemidef_6dd07111738d
-- name    : P2M_GroundTheory_Heights__Heights_GradDensSheetBound_hessC_pm_posSemidef_6dd07111738d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:18:52.606601+00:00
-- url     : https://prove2.me/theorems/a9b45fc7-8090-40a6-aa51-a9d355f342ad
-- title:
--   P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound hess C pm pos Semidef 6dd07111738d: P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound hess C pm pos Semidef 6dd07111738d
-- statement:
--   The P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound hess C pm pos Semidef 6dd07111738d construction uses the P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound hess C pm pos Semidef 6dd07111738d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGradDensSheetBound.lean#L138-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGradDensSheetBound.lean#L138-L203

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGradDensSheetBound
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
open ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.GradDensSheetBound

theorem P2M_GroundTheory_Heights__Heights_GradDensSheetBound_hessC_pm_posSemidef_6dd07111738d {e : ℕ} (φ : (Fin e → ℂ) → ℝ) (x : Fin e → ℂ)
    (h2 : ContDiffAt ℝ 2 φ x) (M c : ℝ) (hM : ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ M) (hc : M / 2 ≤ c) :
    ((c : ℂ) • (1 : Matrix (Fin e) (Fin e) ℂ) - hessC φ x).PosSemidef ∧
      (hessC φ x + (c : ℂ) • (1 : Matrix (Fin e) (Fin e) ℂ)).PosSemidef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GradDensSheetBound».«hessC_pm_posSemidef» := P2M_GroundTheory_Heights__Heights_GradDensSheetBound_hessC_pm_posSemidef_6dd07111738d
