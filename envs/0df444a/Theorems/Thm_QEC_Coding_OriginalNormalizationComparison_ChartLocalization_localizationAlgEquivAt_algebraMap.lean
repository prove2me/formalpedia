-- Prove2me | Theorems.Thm_QEC_Coding_OriginalNormalizationComparison_ChartLocalization_localizationAlgEquivAt_algebraMap
-- name    : QEC.Coding.OriginalNormalizationComparison.ChartLocalization.localizationAlgEquivAt_algebraMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:14:24.210206+00:00
-- url     : https://prove2.me/theorems/a45b70d3-5dd9-4427-849d-b4f74a8913f9
-- title:
--   Chart Localization: localization Alg Equiv At algebra Map
-- statement:
--   The Chart Localization construction uses the localization Alg Equiv At algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLaurentNormalizationComparison.lean#L54-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLaurentNormalizationComparison.lean#L54-L59

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNormalizationComparison
import Mathlib.RingTheory.Localization.BaseChange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLaurentNormalizationComparison
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.OriginalNormalizationComparison QEC.Coding.OriginalNormalizationComparison.ChartLocalization
open scoped TensorProduct
noncomputable section
variable {R S A D : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing D]
  [Algebra R S] [Algebra R A] [Algebra S D]
variable {P U V : Type*} [CommRing P] [CommRing U] [CommRing V]
  [Algebra U V] [Algebra D P]
variable [Algebra S U] [Algebra S V] [Algebra S P]
  [IsScalarTower S U V] [hDP : IsScalarTower S D P]
include hDP

theorem QEC.Coding.OriginalNormalizationComparison.ChartLocalization.localizationAlgEquivAt_algebraMap
    (u : U) (d : D) (f : U ≃ₐ[S] D) (hf : f u = d)
    [IsLocalization.Away u V] [IsLocalization.Away d P] (x : U) :
    localizationAlgEquivAt u d f hf (algebraMap U V x) = algebraMap D P (f x) := by sorry
