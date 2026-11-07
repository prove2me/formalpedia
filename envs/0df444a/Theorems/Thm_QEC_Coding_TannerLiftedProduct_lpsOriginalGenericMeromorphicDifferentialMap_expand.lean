-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGenericMeromorphicDifferentialMap_expand
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGenericMeromorphicDifferentialMap_expand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:15:12.308091+00:00
-- url     : https://prove2.me/theorems/18f931d6-1af3-4155-b1af-44337af1489e
-- title:
--   Tanner Lifted Product: lps Original Generic Meromorphic Differential Map expand
-- statement:
--   Actual original differential compatibility used by the comparison or its semantic fixture.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGenericDifferentialComparison.lean#L230-L239
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGenericDifferentialComparison.lean#L230-L239

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalArithmeticFunctionFieldComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDifferentiation
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericDifferentialComparison
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane TensorProduct
noncomputable section
variable (N : ℕ) (hpos : 0 < N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_135
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_141
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_143
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_145
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_146
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_147
local notation "M" => LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_178
variable [NeZero N]

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGenericMeromorphicDifferentialMap_expand
    (differentialForm : KaehlerDifferential ℂ K) :
    lpsOriginalGenericMeromorphicDifferentialMap N hpos differentialForm =
      lpsOriginalGenericToMeromorphicGerm N hpos
        (lpsOriginalGenericKaehlerCoefficientEquiv N hpos differentialForm) *
          lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
            (lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic) := by sorry
