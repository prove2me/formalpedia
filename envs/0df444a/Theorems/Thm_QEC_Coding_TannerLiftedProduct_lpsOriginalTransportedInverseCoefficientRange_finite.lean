-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTransportedInverseCoefficientRange_finite
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalTransportedInverseCoefficientRange_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:07:34.070871+00:00
-- url     : https://prove2.me/theorems/c808f630-d87d-4246-b0c1-1d3e02f9f0ad
-- title:
--   Tanner Lifted Product: lps Original Transported Inverse Coefficient Range finite
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Transported Inverse Coefficient Range finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalInverseDifferentialLattice.lean#L161-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalInverseDifferentialLattice.lean#L161-L164

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalChartComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInverseDifferentialLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.TannerLiftedProduct
open scoped Polynomial RatFunc
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
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_106
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_107
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_110
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_113
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_114
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_116
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_118
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_120
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_122
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_124
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalTransportedInverseOmegaKModule
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_129
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_131
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_133
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_136
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_138

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalTransportedInverseCoefficientRange_finite :
    Module.Finite P (lpsOriginalTransportedInverseCoefficientMap N hpos).range := by sorry
