-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledProjection_tendsto_codiscrete
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledProjection_tendsto_codiscrete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:02:47.167025+00:00
-- url     : https://prove2.me/theorems/ac46bb10-3881-4c91-b6b2-baba7cd529a2
-- title:
--   Tanner Lifted Product: lps Original Filled Projection tendsto codiscrete
-- statement:
--   The genuine original local quotient transports upstairs codiscreteness to compact-curve codiscreteness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactMeromorphicDifferentialComparison.lean#L813-L848
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactMeromorphicDifferentialComparison.lean#L813-L848

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledProjection_tendsto_codiscrete
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    letI := lpsOriginalFilledTopology N
    Tendsto (fun z : ℂ => lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex z))
      (Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet)
      (Filter.codiscrete (LPSOriginalFilledCurve N)) := by sorry
