-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNativeCovectorToLocal_class
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNativeCovectorToLocal_class
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:22:42.973552+00:00
-- url     : https://prove2.me/theorems/a45d3f44-d1d6-42b2-8561-186f525fc075
-- title:
--   Tanner Lifted Product: lps Original Native Covector To Local class
-- statement:
--   The descended coefficient map evaluates each genuine representative by its actual chart coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeLocalDifferentialComparison.lean#L99-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeLocalDifferentialComparison.lean#L99-L101

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNativeCovectorToLocal_class (σ : Cov) :
    lpsOriginalNativeCovectorToLocal N hN x (lpsOriginalCompactMeromorphicCovectorClass N hN σ) =
      lpsOriginalCovectorRepresentativeToLocal N hN x σ := by sorry
