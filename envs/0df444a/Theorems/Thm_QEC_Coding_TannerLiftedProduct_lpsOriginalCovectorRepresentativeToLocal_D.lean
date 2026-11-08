-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCovectorRepresentativeToLocal_D
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCovectorRepresentativeToLocal_D
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:22:13.243839+00:00
-- url     : https://prove2.me/theorems/0c5e20b4-6036-460d-9ce4-856e6771088a
-- title:
--   Tanner Lifted Product: lps Original Covector Representative To Local D
-- statement:
--   Actual df agrees with differentiation of its actual local function representative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeLocalDifferentialComparison.lean#L105-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeLocalDifferentialComparison.lean#L105-L123

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCovectorRepresentativeToLocal_D
    (F : LPSOriginalFilledMeromorphicFunctionRing N hN) :
    lpsOriginalCovectorRepresentativeToLocal N hN x
      ⟨lpsOriginalFilledFunctionCovector N hN F.val,
        lpsOriginalFilledFunctionCovector_meromorphic N hN F.val F.property⟩ =
      germDerivative a (lpsOriginalRepresentativeToLocal N hN x F) := by sorry
