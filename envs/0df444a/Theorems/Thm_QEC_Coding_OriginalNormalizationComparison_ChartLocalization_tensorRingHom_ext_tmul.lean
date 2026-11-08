-- Prove2me | Theorems.Thm_QEC_Coding_OriginalNormalizationComparison_ChartLocalization_tensorRingHom_ext_tmul
-- name    : QEC.Coding.OriginalNormalizationComparison.ChartLocalization.tensorRingHom_ext_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:12:44.805562+00:00
-- url     : https://prove2.me/theorems/537480e0-1a2d-4a4e-bf51-da74683bfb35
-- title:
--   Chart Localization: tensor Ring Hom ext tmul
-- statement:
--   The Chart Localization construction uses the tensor Ring Hom ext tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLaurentNormalizationComparison.lean#L61-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLaurentNormalizationComparison.lean#L61-L70

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

theorem QEC.Coding.OriginalNormalizationComparison.ChartLocalization.tensorRingHom_ext_tmul {T : Type*} [CommRing T]
    (f h : S ⊗[R] A →+* T) (heq : ∀ c a, f (c ⊗ₜ[R] a) = h (c ⊗ₜ[R] a)) : f = h := by sorry
