-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledDifferentialLinearEquiv_inverse_value
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledDifferentialLinearEquiv_inverse_value
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T04:06:58.122606+00:00
-- url     : https://prove2.me/theorems/e88e03f9-e52a-4b3e-b009-0fd5b4b03939
-- title:
--   Tanner Lifted Product: lps Original Filled Differential Linear Equiv inverse value
-- statement:
--   The inverse equivalence evaluates by the actual tangent derivative of the orbit projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicDifferentialComparison.lean#L889-L903
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicDifferentialComparison.lean#L889-L903

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicDifferentialComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledDifferentialLinearEquiv_inverse_value
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalHolomorphicCovectorSections N hN) (τ : ℍ) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    (lpsOriginalFilledDifferentialLinearEquiv N hN).symm sectionForm τ =
      sectionForm (lpsOriginalHolomorphicCovectorProjection N τ)
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) (lpsOriginalHolomorphicCovectorProjection N) τ (1 : ℂ)) := by sorry
