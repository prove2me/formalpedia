-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRegularKaehler_finiteDimensional
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRegularKaehler_finiteDimensional
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:10:47.83321+00:00
-- url     : https://prove2.me/theorems/91eaf8e6-f223-4405-a581-76691f015f4f
-- title:
--   Tanner Lifted Product: lps Original Regular Kaehler finite Dimensional
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Regular Kaehler finite Dimensional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRegularDifferentialFiniteness.lean#L117-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRegularDifferentialFiniteness.lean#L117-L125

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalChartComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroDifferentialLattice
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInverseDifferentialLattice
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRegularDifferentialFiniteness
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
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
attribute [local instance]
  LPSOriginalLocalKaehlerFinitenessDictionary001
  LPSOriginalLocalKaehlerFinitenessDictionary002
  LPSOriginalLocalKaehlerFinitenessDictionary003
  LPSOriginalLocalKaehlerFinitenessDictionary004
  LPSOriginalLocalKaehlerFinitenessDictionary005
  LPSOriginalLocalKaehlerFinitenessDictionary006
  LPSOriginalLocalKaehlerFinitenessDictionary007
  LPSOriginalLocalKaehlerFinitenessDictionary008
  LPSOriginalLocalKaehlerFinitenessDictionary009
  LPSOriginalLocalKaehlerFinitenessDictionary010
  LPSOriginalLocalKaehlerFinitenessDictionary011
  LPSOriginalLocalKaehlerFinitenessDictionary012
  LPSOriginalLocalKaehlerFinitenessDictionary013
  LPSOriginalLocalKaehlerFinitenessDictionary014
  LPSOriginalLocalKaehlerFinitenessDictionary015
  LPSOriginalLocalKaehlerFinitenessDictionary016
  LPSOriginalLocalKaehlerFinitenessDictionary017
  LPSOriginalLocalKaehlerFinitenessDictionary018
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
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_58
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_59
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_60
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_61
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_63
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_65
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_67
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_70
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_71
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_73
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_75

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRegularKaehler_finiteDimensional :
    FiniteDimensional ℂ (lpsOriginalNativeRegularKaehlerSubmodule N hpos) := by sorry
