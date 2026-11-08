-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCovectorRepresentativeToLocal_functionTimes
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCovectorRepresentativeToLocal_functionTimes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:21:47.531914+00:00
-- url     : https://prove2.me/theorems/3940a8d3-469c-4f36-ac00-0b1d9469162f
-- title:
--   Tanner Lifted Product: lps Original Covector Representative To Local function Times
-- statement:
--   Pointwise multiplication becomes actual multiplication of local coefficient germs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeLocalDifferentialComparison.lean#L126-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeLocalDifferentialComparison.lean#L126-L138

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalRegularDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericCompactDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeLocalDifferentialComparison
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) (x : LPSOriginalFilledCurve N)
local notation "a" => lpsOriginalLocalChartCenter N hN x
local notation "G" => MeromorphicGermRing a
local notation "Cov" => LPSOriginalFilledMeromorphicCovectorRepresentatives N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_26
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_28

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCovectorRepresentativeToLocal_functionTimes
    (F : LPSOriginalFilledMeromorphicFunctionRing N hN) (σ : Cov) :
    lpsOriginalCovectorRepresentativeToLocal N hN x
      (lpsOriginalFilledMeromorphicFunctionTimesCovector N hN F σ) =
      lpsOriginalRepresentativeToLocal N hN x F *
        lpsOriginalCovectorRepresentativeToLocal N hN x σ := by sorry
