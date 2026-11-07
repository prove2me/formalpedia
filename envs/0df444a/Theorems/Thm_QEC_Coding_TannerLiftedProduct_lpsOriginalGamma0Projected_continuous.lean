-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGamma0Projected_continuous
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGamma0Projected_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:37:54.638897+00:00
-- url     : https://prove2.me/theorems/f4f11618-e8ea-4e0e-9587-624ca87519f3
-- title:
--   Tanner Lifted Product: lps Original Gamma0 Projected continuous
-- statement:
--   The genuine original integral projection is continuous.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactCore.lean#L30-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactCore.lean#L30-L32

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGamma0Projected_continuous (N : ℕ) (ρ : SL(2,ℤ)) :
    Continuous (lpsOriginalGamma0Projected N ρ) := by sorry
