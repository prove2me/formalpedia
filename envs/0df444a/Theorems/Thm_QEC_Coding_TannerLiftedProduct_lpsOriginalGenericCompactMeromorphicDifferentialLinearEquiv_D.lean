-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_D
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_D
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:51:54.906796+00:00
-- url     : https://prove2.me/theorems/52fb3ad2-9a83-4e21-918c-a96d254bf0c6
-- title:
--   Tanner Lifted Product: lps Original Generic Compact Meromorphic Differential Linear Equiv D
-- statement:
--   For EVERY field element and EVERY actual representative, universal df maps to the actual manifold derivative dF.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGenericCompactDifferentialComparison.lean#L113-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGenericCompactDifferentialComparison.lean#L113-L142

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_D
    (f : K) (F : LPSOriginalFilledMeromorphicFunctionRing N hN)
    (hF : lpsOriginalCompactMeromorphicGermAlgHom N hN F =
      lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN f) :
    lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN
      (KaehlerDifferential.D ℂ K f) =
        lpsOriginalCompactMeromorphicCovectorClass N hN
          ⟨lpsOriginalFilledFunctionCovector N hN F.val,
            lpsOriginalFilledFunctionCovector_meromorphic N hN F.val F.property⟩ := by sorry
