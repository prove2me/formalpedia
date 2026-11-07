-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGamma0Quotient_t2
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGamma0Quotient_t2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:38:19.873486+00:00
-- url     : https://prove2.me/theorems/da0ff9ac-45ce-4176-a186-019e69883527
-- title:
--   Tanner Lifted Product: lps Original Gamma0 Quotient t2
-- statement:
--   The actual original quotient is Hausdorff by its genuine arithmetic properly discontinuous action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactCore.lean#L93-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactCore.lean#L93-L98

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGamma0Quotient_t2 (N : ℕ) [NeZero N] :
    T2Space (MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) := by sorry
