-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_injective_a51db807acbc
-- name    : P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_injective_a51db807acbc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:20.755241+00:00
-- url     : https://prove2.me/theorems/48054d35-d47c-4a4e-885e-d0e0e52ec5f4
-- title:
--   P2 M Ground Theory Heights  Heights Normalisation Model Localization loc To Frac injective a51db807acbc: P2 M Ground Theory Heights  Heights Normalisation Model Localization loc To Frac injective a51d
-- statement:
--   The P2 M Ground Theory Heights  Heights Normalisation Model Localization loc To Frac injective a51db807acbc construction uses the P2 M Ground Theory Heights  Heights Normalisation Model Localization loc To Frac injective a51db807acbc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PNormalisationModelLocalizationX.lean#L217-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PNormalisationModelLocalizationX.lean#L217-L223

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

theorem P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_injective_a51db807acbc (hJ : J.IsPrime) (hq : q ∈ zeroSet J) : Function.Injective (locToFrac M hJ hq) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalisationModelLocalization».«locToFrac_injective» := P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_injective_a51db807acbc
