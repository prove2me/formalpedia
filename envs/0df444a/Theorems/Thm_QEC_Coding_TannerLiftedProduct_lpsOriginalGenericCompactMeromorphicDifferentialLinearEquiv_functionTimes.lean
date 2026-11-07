-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_functionTimes
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_functionTimes
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:59:24.549713+00:00
-- url     : https://prove2.me/theorems/221d6a9d-6238-4ce2-9b96-1c1435c77ff6
-- title:
--   Tanner Lifted Product: lps Original Generic Compact Meromorphic Differential Linear Equiv function Times
-- statement:
--   Generic scalar multiplication agrees with actual pointwise function multiplication of arbitrary native representatives.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGenericCompactDifferentialComparison.lean#L176-L197
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGenericCompactDifferentialComparison.lean#L176-L197

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericCompactDifferentialComparison
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane Manifold ContDiff TensorProduct
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_f7e67548a0_28
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "L" => LPSOriginalCompactMeromorphicGermRing N hN
local notation "M" => LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_f7e67548a0_35
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_f7e67548a0_36
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_f7e67548a0_37
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_f7e67548a0_70
local notation "V" => LPSOriginalFilledMeromorphicCovectorRepresentatives N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_f7e67548a0_74

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_functionTimes
    (f : K) (differentialForm : KaehlerDifferential ℂ K)
    (F : LPSOriginalFilledMeromorphicFunctionRing N hN)
    (sectionForm : LPSOriginalFilledMeromorphicCovectorRepresentatives N hN)
    (hF : lpsOriginalCompactMeromorphicGermAlgHom N hN F =
      lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN f)
    (hsection : lpsOriginalCompactMeromorphicCovectorClass N hN sectionForm =
      lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN differentialForm) :
    lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN (f • differentialForm) =
      lpsOriginalCompactMeromorphicCovectorClass N hN
        (lpsOriginalFilledMeromorphicFunctionTimesCovector N hN F sectionForm) := by sorry
