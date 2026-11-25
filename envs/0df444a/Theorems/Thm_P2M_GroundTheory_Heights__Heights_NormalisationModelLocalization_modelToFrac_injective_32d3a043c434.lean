-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_modelToFrac_injective_32d3a043c434
-- name    : P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_modelToFrac_injective_32d3a043c434
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:05:34.512805+00:00
-- url     : https://prove2.me/theorems/890dc7c0-a9fa-468b-ac4f-f40d3469770a
-- title:
--   P2 M Ground Theory Heights  Heights Normalisation Model Localization model To Frac injective 32d3a043c434: P2 M Ground Theory Heights  Heights Normalisation Model Localization model To Frac injective
-- statement:
--   The P2 M Ground Theory Heights  Heights Normalisation Model Localization model To Frac injective 32d3a043c434 construction uses the P2 M Ground Theory Heights  Heights Normalisation Model Localization model To Frac injective 32d3a043c434 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PNormalisationModelLocalizationX.lean#L191-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PNormalisationModelLocalizationX.lean#L191-L196

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

theorem P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_modelToFrac_injective_32d3a043c434 (hJ : J.IsPrime) (hq : q ∈ zeroSet J) : Function.Injective (modelToFrac M hJ hq) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalisationModelLocalization».«modelToFrac_injective» := P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_modelToFrac_injective_32d3a043c434
