-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradDensSheetBound_exists_hessC_bound_31a6c909ca72
-- name    : P2M_GroundTheory_Heights__Heights_GradDensSheetBound_exists_hessC_bound_31a6c909ca72
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:18:56.524406+00:00
-- url     : https://prove2.me/theorems/67108958-6f3f-43da-aca8-b8a354d44394
-- title:
--   P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound exists hess C bound 31a6c909ca72: P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound exists hess C bound 31a6c909ca72
-- statement:
--   The P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound exists hess C bound 31a6c909ca72 construction uses the P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound exists hess C bound 31a6c909ca72 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGradDensSheetBound.lean#L205-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGradDensSheetBound.lean#L205-L222

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

theorem P2M_GroundTheory_Heights__Heights_GradDensSheetBound_exists_hessC_bound_31a6c909ca72 {n d : ℕ} (φ : Fin d → (Fin n → ℂ) → ℝ) (U K : Set (Fin n → ℂ))
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (hφ : ∀ i, ContDiffOn ℝ 2 (φ i) U) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ i,
      ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - hessC (φ i) x).PosSemidef ∧
        (hessC (φ i) x + (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GradDensSheetBound».«exists_hessC_bound» := P2M_GroundTheory_Heights__Heights_GradDensSheetBound_exists_hessC_bound_31a6c909ca72
