-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCompactMeromorphicCovectorRatioMap_dj
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCompactMeromorphicCovectorRatioMap_dj
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T04:10:42.315136+00:00
-- url     : https://prove2.me/theorems/fec7c0e4-7876-4256-ad7a-649a60b70493
-- title:
--   Tanner Lifted Product: lps Original Compact Meromorphic Covector Ratio Map dj
-- statement:
--   Actual original differential compatibility used by the comparison or its semantic fixture.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactMeromorphicDifferentialComparison.lean#L797-L808
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactMeromorphicDifferentialComparison.lean#L797-L808

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCompactMeromorphicCovectorRatioMap_dj :
    lpsOriginalCompactMeromorphicCovectorRatioMap N hN
      ⟨lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N),
        lpsOriginalFilledFunctionCovector_meromorphic N hN (lpsOriginalFilledJ N)
          (lpsOriginalFilledChartMeromorphic_j N hN)⟩ = 1 := by sorry
