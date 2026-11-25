-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradDensSheetBound_mdisc_cons_smul_tail_e30b329eeb60
-- name    : P2M_GroundTheory_Heights__Heights_GradDensSheetBound_mdisc_cons_smul_tail_e30b329eeb60
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:18:23.506418+00:00
-- url     : https://prove2.me/theorems/28ced8e3-852c-4261-9e47-3c987c442306
-- title:
--   P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound mdisc cons smul tail e30b329eeb60: P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound mdisc cons smul tail e30b329eeb60
-- statement:
--   The P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound mdisc cons smul tail e30b329eeb60 construction uses the P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound mdisc cons smul tail e30b329eeb60 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGradDensSheetBound.lean#L16-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGradDensSheetBound.lean#L16-L29

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

theorem P2M_GroundTheory_Heights__Heights_GradDensSheetBound_mdisc_cons_smul_tail_e30b329eeb60 {n : ℕ} (c : ℂ) (hc : c ≠ 0)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (W : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons X (fun i => c • W i) : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      c ^ n * mdisc (Fin.cons X W : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GradDensSheetBound».«mdisc_cons_smul_tail» := P2M_GroundTheory_Heights__Heights_GradDensSheetBound_mdisc_cons_smul_tail_e30b329eeb60
