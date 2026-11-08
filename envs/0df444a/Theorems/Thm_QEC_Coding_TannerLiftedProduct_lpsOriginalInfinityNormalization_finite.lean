-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityNormalization_finite
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityNormalization_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:10:40.194984+00:00
-- url     : https://prove2.me/theorems/3a33f67d-313c-4f9f-8b64-a2c660eef2da
-- title:
--   Tanner Lifted Product: lps Original Infinity Normalization finite
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Infinity Normalization finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalInverseDifferentialLattice.lean#L69-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalInverseDifferentialLattice.lean#L69-L70

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalChartComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInverseDifferentialLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.TannerLiftedProduct
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "P" => Polynomial ℂ
local notation "J" => FractionRing P
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
attribute [local instance]
  LPSOriginalLocalKaehlerFinitenessDictionary027
  LPSOriginalLocalKaehlerFinitenessDictionary029
  LPSOriginalLocalKaehlerFinitenessDictionary031
  LPSOriginalLocalKaehlerFinitenessDictionary032
  LPSOriginalLocalKaehlerFinitenessDictionary033
  LPSOriginalLocalKaehlerFinitenessDictionary034
  LPSOriginalLocalKaehlerFinitenessDictionary035
  LPSOriginalLocalKaehlerFinitenessDictionary036
  LPSOriginalLocalKaehlerFinitenessDictionary037
  LPSOriginalLocalKaehlerFinitenessDictionary038
  LPSOriginalLocalKaehlerFinitenessDictionary039
  LPSOriginalLocalKaehlerFinitenessDictionary040
  LPSOriginalLocalKaehlerFinitenessDictionary041
  LPSOriginalLocalKaehlerFinitenessDictionary042
  LPSOriginalLocalKaehlerFinitenessDictionary043
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_41
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_42
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_43
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_44
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_45
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_46
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_47
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_48
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_49
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_54
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_56
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_58
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_60
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_62
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_64
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_66

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityNormalization_finite : Module.Finite P R := by sorry
