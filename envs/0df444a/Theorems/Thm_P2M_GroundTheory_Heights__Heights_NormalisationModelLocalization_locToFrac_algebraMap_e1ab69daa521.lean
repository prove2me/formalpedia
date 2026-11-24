-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_algebraMap_e1ab69daa521
-- name    : P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_algebraMap_e1ab69daa521
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:08.374055+00:00
-- url     : https://prove2.me/theorems/6c5b6f7e-18e2-4327-8a7b-fde5b0076894
-- title:
--   P2 M Ground Theory Heights  Heights Normalisation Model Localization loc To Frac algebra Map e1ab69daa521: P2 M Ground Theory Heights  Heights Normalisation Model Localization loc To Frac algebra Map
-- statement:
--   The P2 M Ground Theory Heights  Heights Normalisation Model Localization loc To Frac algebra Map e1ab69daa521 construction uses the P2 M Ground Theory Heights  Heights Normalisation Model Localization loc To Frac algebra Map e1ab69daa521 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PNormalisationModelLocalizationX.lean#L212-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PNormalisationModelLocalizationX.lean#L212-L215

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

theorem P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_algebraMap_e1ab69daa521 (hJ : J.IsPrime) (hq : q ∈ zeroSet J) (r : MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) :
    locToFrac M hJ hq (algebraMap _ _ r) = modelToFrac M hJ hq r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalisationModelLocalization».«locToFrac_algebraMap» := P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_algebraMap_e1ab69daa521
