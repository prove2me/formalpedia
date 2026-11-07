-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledInteriorChart_projection_differential
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledInteriorChart_projection_differential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:07:45.221246+00:00
-- url     : https://prove2.me/theorems/6a1d85ef-e2b0-4596-954b-c10e8d97cd1a
-- title:
--   Tanner Lifted Product: lps Original Filled Interior Chart projection differential
-- statement:
--   The original interior chart pulls its coefficient back to the original cusp form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledDifferential.lean#L111-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledDifferential.lean#L111-L157

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialGluing
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledDifferential
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledInteriorChart_projection_differential (N : ℕ) [NeZero N]
    (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (τ : ℍ) (hs : letI := lpsOriginalFilledTopology N
      Sum.inl (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ)∈
        (lpsOriginalFilledInteriorChart N hN x).source) :
    letI := lpsOriginalFilledTopology N
    let Φ : ℂ→ℂ := fun z => lpsOriginalFilledInteriorChart N hN x
      (Sum.inl (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
        (UpperHalfPlane.ofComplex z)))
    f (UpperHalfPlane.ofComplex (Φ τ)) * deriv Φ τ = f τ := by sorry
