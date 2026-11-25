-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_toFracModel_mem_e173d248237c
-- name    : P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_toFracModel_mem_e173d248237c
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:06:54.201652+00:00
-- url     : https://prove2.me/theorems/3170599d-9070-495c-a99c-9110048399b5
-- title:
--   P2 M Ground Theory Heights  Heights Normalisation Model Localization to Frac Model mem e173d248237c: P2 M Ground Theory Heights  Heights Normalisation Model Localization to Frac Model mem e173d248237c
-- statement:
--   The P2 M Ground Theory Heights  Heights Normalisation Model Localization to Frac Model mem e173d248237c construction uses the P2 M Ground Theory Heights  Heights Normalisation Model Localization to Frac Model mem e173d248237c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PNormalisationModelLocalizationX.lean#L261-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PNormalisationModelLocalizationX.lean#L261-L294

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

theorem P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_toFracModel_mem_e173d248237c (hJ : J.IsPrime) (hq : q ∈ zeroSet J) (h : MvPolynomial (Fin n ⊕ Fin M.m) ℂ) :
    toFracModel M q h ∈ integralClosure (curveLocalRing J q) (FractionRing (curveLocalRing J q)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalisationModelLocalization».«toFracModel_mem» := P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_toFracModel_mem_e173d248237c
