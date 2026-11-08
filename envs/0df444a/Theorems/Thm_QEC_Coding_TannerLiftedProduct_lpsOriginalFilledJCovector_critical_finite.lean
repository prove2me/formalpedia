-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJCovector_critical_finite
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJCovector_critical_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:10:34.984739+00:00
-- url     : https://prove2.me/theorems/d94db8a0-cc38-483d-a1de-48d254865094
-- title:
--   Tanner Lifted Product: lps Original Filled JCovector critical finite
-- statement:
--   Compactness makes the actual zero-unit-evaluation set of dj finite, including its pole representative points.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactMeromorphicDifferentialComparison.lean#L454-L466
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactMeromorphicDifferentialComparison.lean#L454-L466

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJCovector_critical_finite
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    {y : LPSOriginalFilledCurve N |
      lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N) y (1 : ℂ) = 0}.Finite := by sorry
