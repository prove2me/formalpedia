-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCompactMeromorphicCovectorLinearEquiv_class
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCompactMeromorphicCovectorLinearEquiv_class
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:10:07.765275+00:00
-- url     : https://prove2.me/theorems/75c5cc0f-5988-44a4-be9f-14856001b676
-- title:
--   Tanner Lifted Product: lps Original Compact Meromorphic Covector Linear Equiv class
-- statement:
--   Actual original differential compatibility used by the comparison or its semantic fixture.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactMeromorphicDifferentialComparison.lean#L759-L763
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactMeromorphicDifferentialComparison.lean#L759-L763

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDifferentiation
import Mathlib.LinearAlgebra.Isomorphisms
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicDifferentialComparison
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane Manifold
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)
local notation "R" => LPSOriginalFilledMeromorphicFunctionRing N hN
local notation "L" => LPSOriginalCompactMeromorphicGermRing N hN
local notation "V" => LPSOriginalFilledMeromorphicCovectorRepresentatives N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_391f8f7aa3_629
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_391f8f7aa3_630
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCompactMeromorphicCovectorLinearEquiv_class (sectionForm : V) :
    lpsOriginalCompactMeromorphicCovectorLinearEquiv N hN
      (lpsOriginalCompactMeromorphicCovectorClass N hN sectionForm) =
        lpsOriginalCompactMeromorphicCovectorRatioMap N hN sectionForm := by sorry
