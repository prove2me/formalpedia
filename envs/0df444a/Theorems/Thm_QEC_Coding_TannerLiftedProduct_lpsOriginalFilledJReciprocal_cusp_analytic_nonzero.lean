-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJReciprocal_cusp_analytic_nonzero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJReciprocal_cusp_analytic_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:01:45.039543+00:00
-- url     : https://prove2.me/theorems/8b32d547-e515-4edb-8559-b30bf0b1ed1e
-- title:
--   Tanner Lifted Product: lps Original Filled JReciprocal cusp analytic nonzero
-- statement:
--   Actual nonzero cusp-target analyticity via true original interior overlap.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L134-L156
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L134-L156

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJReciprocal_cusp_analytic_nonzero (N : ℕ) [NeZero N]
    (hN : 4∣N) (a : ℂ) (ho : ∀ τ : ℍ, lpsOriginalJInvariant τ≠a)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (z : ℂ) (hz : z∈(lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)
    (hz0 : z≠0) :
    letI := lpsOriginalFilledTopology N
    AnalyticAt ℂ (fun w : ℂ => lpsOriginalFilledJReciprocal N a
      ((lpsOriginalFilledCuspChart N c).symm w)) z := by sorry
