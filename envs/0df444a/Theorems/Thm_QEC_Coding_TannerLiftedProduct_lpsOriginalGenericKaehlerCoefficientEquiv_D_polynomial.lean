-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGenericKaehlerCoefficientEquiv_D_polynomial
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGenericKaehlerCoefficientEquiv_D_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:19:02.052611+00:00
-- url     : https://prove2.me/theorems/e21e2b48-0ec4-407e-b079-f484cf7bae87
-- title:
--   Tanner Lifted Product: lps Original Generic Kaehler Coefficient Equiv D polynomial
-- statement:
--   Actual original differential compatibility used by the comparison or its semantic fixture.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGenericDifferentialComparison.lean#L89-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGenericDifferentialComparison.lean#L89-L100

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalArithmeticFunctionFieldComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDifferentiation
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericDifferentialComparison
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
variable (N : ℕ) (hpos : 0 < N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_31
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_37
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_39
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_41
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_42
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_43
variable [NeZero N]

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGenericKaehlerCoefficientEquiv_D_polynomial (p : Polynomial ℂ) :
    lpsOriginalGenericKaehlerCoefficientEquiv N hpos
      (KaehlerDifferential.D ℂ K (algebraMap P K p)) =
        algebraMap P K p.derivative := by sorry
