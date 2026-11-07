-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphicPullback_eventually_regular
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphicPullback_eventually_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:05:17.56767+00:00
-- url     : https://prove2.me/theorems/36b31b52-89ae-438b-86ca-9e7aec56b694
-- title:
--   Tanner Lifted Product: lps Original Filled Meromorphic Pullback eventually regular
-- statement:
--   Actual original differential compatibility used by the comparison or its semantic fixture.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactMeromorphicDifferentialComparison.lean#L851-L867
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactMeromorphicDifferentialComparison.lean#L851-L867

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphicPullback_eventually_regular
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    ∀ᶠ z in Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet,
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F
        (lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex z)) := by sorry
