-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJComplexDerivative_eventually_ne_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJComplexDerivative_eventually_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:06:41.024896+00:00
-- url     : https://prove2.me/theorems/a079aa66-b816-4ed2-a97e-b74d66203f45
-- title:
--   Tanner Lifted Product: lps Original JComplex Derivative eventually ne zero
-- statement:
--   Actual original differential compatibility used by the comparison or its semantic fixture.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactMeromorphicDifferentialComparison.lean#L907-L918
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactMeromorphicDifferentialComparison.lean#L907-L918

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJComplexDerivative_eventually_ne_zero :
    ∀ᶠ z in Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet,
      deriv (lpsOriginalJInvariant ∘ UpperHalfPlane.ofComplex) z ≠ 0 := by sorry
