-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_exists_locToFrac_33b3ccc2644e
-- name    : P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_exists_locToFrac_33b3ccc2644e
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:06:46.081144+00:00
-- url     : https://prove2.me/theorems/7cf388a1-c3e0-49b0-afb9-67b48d128c1c
-- title:
--   P2 M Ground Theory Heights  Heights Normalisation Model Localization exists loc To Frac 33b3ccc2644e: P2 M Ground Theory Heights  Heights Normalisation Model Localization exists loc To Frac 33b3ccc264
-- statement:
--   The P2 M Ground Theory Heights  Heights Normalisation Model Localization exists loc To Frac 33b3ccc2644e construction uses the P2 M Ground Theory Heights  Heights Normalisation Model Localization exists loc To Frac 33b3ccc2644e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PNormalisationModelLocalizationX.lean#L311-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PNormalisationModelLocalizationX.lean#L311-L347

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

theorem P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_exists_locToFrac_33b3ccc2644e (hJ : J.IsPrime) (hq : q ∈ zeroSet J) (x : FractionRing (curveLocalRing J q))
    (hx : IsIntegral (curveLocalRing J q) x) : ∃ z, locToFrac M hJ hq z = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalisationModelLocalization».«exists_locToFrac» := P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_exists_locToFrac_33b3ccc2644e
