-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradDensSheetBound_posSemidef_transpose_mul_mul_conj_ecf514a418de
-- name    : P2M_GroundTheory_Heights__Heights_GradDensSheetBound_posSemidef_transpose_mul_mul_conj_ecf514a418de
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:18:36.236347+00:00
-- url     : https://prove2.me/theorems/92a21673-bb58-4e55-9089-f4e90708319a
-- title:
--   P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound pos Semidef transpose mul mul conj ecf514a418de: P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound pos Semidef transpose mul mul conj
-- statement:
--   The P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound pos Semidef transpose mul mul conj ecf514a418de construction uses the P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound pos Semidef transpose mul mul conj ecf514a418de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGradDensSheetBound.lean#L224-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGradDensSheetBound.lean#L224-L230

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

theorem P2M_GroundTheory_Heights__Heights_GradDensSheetBound_posSemidef_transpose_mul_mul_conj_ecf514a418de {n m : ℕ} (J : Matrix (Fin n) (Fin m) ℂ)
    {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosSemidef) :
    (Jᵀ * P * J.map (starRingEnd ℂ)).PosSemidef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GradDensSheetBound».«posSemidef_transpose_mul_mul_conj» := P2M_GroundTheory_Heights__Heights_GradDensSheetBound_posSemidef_transpose_mul_mul_conj_ecf514a418de
