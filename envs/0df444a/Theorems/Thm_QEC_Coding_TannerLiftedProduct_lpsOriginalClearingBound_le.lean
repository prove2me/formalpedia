-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearingBound_le
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearingBound_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:57:39.07471+00:00
-- url     : https://prove2.me/theorems/74b50580-1369-4a6c-8104-c7c13e2caad1
-- title:
--   Tanner Lifted Product: lps Original Clearing Bound le
-- statement:
--   Every genuinely supported weighted exponent is bounded by that finite supremum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L293-L299
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L293-L299

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearingBound_le (N : ℕ) (P : Polynomial (Polynomial ℂ))
    {k i : ℕ} (hk : k∈P.support) (hi : i∈(P.coeff k).support) :
    i+N*k≤lpsOriginalClearingBound N P := by sorry
