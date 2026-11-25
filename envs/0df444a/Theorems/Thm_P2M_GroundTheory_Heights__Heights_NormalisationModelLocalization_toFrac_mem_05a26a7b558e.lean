-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_toFrac_mem_05a26a7b558e
-- name    : P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_toFrac_mem_05a26a7b558e
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:06:54.497332+00:00
-- url     : https://prove2.me/theorems/16a298f0-8e90-4d45-81f4-edfa999ce245
-- title:
--   P2 M Ground Theory Heights  Heights Normalisation Model Localization to Frac mem 05a26a7b558e: P2 M Ground Theory Heights  Heights Normalisation Model Localization to Frac mem 05a26a7b558e
-- statement:
--   The P2 M Ground Theory Heights  Heights Normalisation Model Localization to Frac mem 05a26a7b558e construction uses the P2 M Ground Theory Heights  Heights Normalisation Model Localization to Frac mem 05a26a7b558e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PNormalisationModelLocalizationX.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PNormalisationModelLocalizationX.lean#L48-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalisationModelLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PNormalisationModelLocalizationX
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
open MvPolynomial ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.NormalisationModelLocalization
variable {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}

theorem P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_toFrac_mem_05a26a7b558e (f : MvPolynomial (Fin n) ℂ) :
    toFrac J q f ∈ integralClosure (curveLocalRing J q) (FractionRing (curveLocalRing J q)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalisationModelLocalization».«toFrac_mem» := P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_toFrac_mem_05a26a7b558e
