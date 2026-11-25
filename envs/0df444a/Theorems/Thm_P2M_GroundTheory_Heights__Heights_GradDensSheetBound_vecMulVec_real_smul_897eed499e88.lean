-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradDensSheetBound_vecMulVec_real_smul_897eed499e88
-- name    : P2M_GroundTheory_Heights__Heights_GradDensSheetBound_vecMulVec_real_smul_897eed499e88
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:22.844866+00:00
-- url     : https://prove2.me/theorems/09279f27-d8fc-4616-89d4-50f6bbea3389
-- title:
--   P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound vec Mul Vec real smul 897eed499e88: P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound vec Mul Vec real smul 897eed499e88
-- statement:
--   The P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound vec Mul Vec real smul 897eed499e88 construction uses the P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound vec Mul Vec real smul 897eed499e88 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGradDensSheetBound.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGradDensSheetBound.lean#L31-L35

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

theorem P2M_GroundTheory_Heights__Heights_GradDensSheetBound_vecMulVec_real_smul_897eed499e88 {m : ℕ} (r r' : ℝ) (a b : Fin m → ℂ) :
    vecMulVec ((r : ℂ) • a) (star ((r' : ℂ) • b)) = ((r * r' : ℝ) : ℂ) • vecMulVec a (star b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GradDensSheetBound».«vecMulVec_real_smul» := P2M_GroundTheory_Heights__Heights_GradDensSheetBound_vecMulVec_real_smul_897eed499e88
