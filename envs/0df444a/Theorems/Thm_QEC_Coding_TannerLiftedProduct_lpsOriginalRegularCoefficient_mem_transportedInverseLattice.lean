-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRegularCoefficient_mem_transportedInverseLattice
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRegularCoefficient_mem_transportedInverseLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:08:54.206277+00:00
-- url     : https://prove2.me/theorems/8bff7795-0b91-4c2f-acbc-3b04a37b343d
-- title:
--   Tanner Lifted Product: lps Original Regular Coefficient mem transported Inverse Lattice
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Regular Coefficient mem transported Inverse Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalInverseDifferentialLattice.lean#L166-L171
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalInverseDifferentialLattice.lean#L166-L171

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRegularCoefficient_mem_transportedInverseLattice
    (omega : lpsOriginalNativeRegularKaehlerSubmodule N hpos) :
    lpsOriginalGenericKaehlerCoefficientEquiv N hpos omega.val ∈
      (lpsOriginalTransportedInverseCoefficientMap N hpos).range := by sorry
