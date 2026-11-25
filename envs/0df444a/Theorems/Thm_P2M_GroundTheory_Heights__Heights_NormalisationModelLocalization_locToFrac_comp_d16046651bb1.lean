-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_comp_d16046651bb1
-- name    : P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_comp_d16046651bb1
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:05:49.636292+00:00
-- url     : https://prove2.me/theorems/20eb6aea-5480-4a09-9b68-83cccd4c4b49
-- title:
--   P2 M Ground Theory Heights  Heights Normalisation Model Localization loc To Frac comp d16046651bb1: P2 M Ground Theory Heights  Heights Normalisation Model Localization loc To Frac comp d16046651bb1
-- statement:
--   The P2 M Ground Theory Heights  Heights Normalisation Model Localization loc To Frac comp d16046651bb1 construction uses the P2 M Ground Theory Heights  Heights Normalisation Model Localization loc To Frac comp d16046651bb1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PNormalisationModelLocalizationX.lean#L253-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PNormalisationModelLocalizationX.lean#L253-L259

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
variable (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
variable {M}
variable (M)

theorem P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_comp_d16046651bb1 (hJ : J.IsPrime) (hq : q ∈ zeroSet J) :
    (locToFrac M hJ hq).comp (locToModel M) = algebraMap (curveLocalRing J q) (FractionRing (curveLocalRing J q)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalisationModelLocalization».«locToFrac_comp» := P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_comp_d16046651bb1
