-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_ratio
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:49:51.06148+00:00
-- url     : https://prove2.me/theorems/8af9cc15-373c-4363-afe2-274f80776c30
-- title:
--   Tanner Lifted Product: lps Original Generic Compact Meromorphic Differential Linear Equiv ratio
-- statement:
--   Actual original differential compatibility used by the comparison or its semantic fixture.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGenericCompactDifferentialComparison.lean#L103-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGenericCompactDifferentialComparison.lean#L103-L109

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_ratio
    (differentialForm : KaehlerDifferential ℂ K) :
    lpsOriginalCompactMeromorphicCovectorLinearEquiv N hN
      (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN differentialForm) =
        lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN
          (lpsOriginalGenericKaehlerCoefficientEquiv N hpos differentialForm) := by sorry
