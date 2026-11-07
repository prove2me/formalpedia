-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCompactMeromorphicCovectorRatioMap_D_restrict
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCompactMeromorphicCovectorRatioMap_D_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:14:18.656604+00:00
-- url     : https://prove2.me/theorems/a218ea10-1107-4908-803a-b8af8ce7fba5
-- title:
--   Tanner Lifted Product: lps Original Compact Meromorphic Covector Ratio Map D restrict
-- statement:
--   The ratio of the actual dF, restricted upstairs, times actual j derivative equals actual F derivative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactMeromorphicDifferentialComparison.lean#L970-L1019
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactMeromorphicDifferentialComparison.lean#L970-L1019

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
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCompactMeromorphicCovectorRatioMap_D_restrict
    (F : R) :
    (lpsOriginalCompactToRestrictedMeromorphic N hN
      (lpsOriginalCompactMeromorphicCovectorRatioMap N hN
        ⟨lpsOriginalFilledFunctionCovector N hN F.val,
          lpsOriginalFilledFunctionCovector_meromorphic N hN F.val F.property⟩)).val *
      lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
        (lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic) =
      lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
        (lpsOriginalFilledMeromorphicRestriction N hN F.val F.property).val := by sorry
