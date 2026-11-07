-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGamma0_projected_im_bound
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGamma0_projected_im_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:38:08.863957+00:00
-- url     : https://prove2.me/theorems/33756764-00ab-4d08-ba0e-219f080573e7
-- title:
--   Tanner Lifted Product: lps Original Gamma0 projected im bound
-- statement:
--   The original quotient equality implies the genuine integral upper bound on cusp height.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactCore.lean#L133-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactCore.lean#L133-L153

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGamma0_projected_im_bound (N : ℕ) (ρ : SL(2,ℤ)) (τ σ : ℍ)
    (h : lpsOriginalGamma0Projected N ρ τ=
      (⟦σ⟧ : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)) :
    τ.im≤ max σ.im (1/σ.im) := by sorry
