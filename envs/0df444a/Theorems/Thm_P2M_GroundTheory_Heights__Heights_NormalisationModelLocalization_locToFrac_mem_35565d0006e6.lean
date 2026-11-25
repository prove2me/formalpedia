-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_mem_35565d0006e6
-- name    : P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_mem_35565d0006e6
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:05:01.528907+00:00
-- url     : https://prove2.me/theorems/321a9105-aed9-554f-a9ca-dd10e99edd5b
-- title:
--   P2 M Ground Theory Heights  Heights Normalisation Model Localization loc To Frac mem 35565d0006e6: P2 M Ground Theory Heights  Heights Normalisation Model Localization loc To Frac mem 35565d0006e6
-- statement:
--   The P2 M Ground Theory Heights  Heights Normalisation Model Localization loc To Frac mem 35565d0006e6 construction uses the P2 M Ground Theory Heights  Heights Normalisation Model Localization loc To Frac mem 35565d0006e6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PNormalisationModelLocalizationX.lean#L296-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PNormalisationModelLocalizationX.lean#L296-L309

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

theorem P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_mem_35565d0006e6 (hJ : J.IsPrime) (hq : q ∈ zeroSet J) (z : Localization (normalModelSubmonoid M q)) :
    locToFrac M hJ hq z ∈ integralClosure (curveLocalRing J q) (FractionRing (curveLocalRing J q)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalisationModelLocalization».«locToFrac_mem» := P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_mem_35565d0006e6
