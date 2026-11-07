-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledDifferential_projection_pullback
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledDifferential_projection_pullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:07:41.201072+00:00
-- url     : https://prove2.me/theorems/4500084e-5cea-42e9-8623-20f00f19d36b
-- title:
--   Tanner Lifted Product: lps Original Filled Differential projection pullback
-- statement:
--   The actual orbit-projection tangent map pulls the global covector back to the original differential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledDifferential.lean#L160-L192
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledDifferential.lean#L160-L192

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledDifferential_projection_pullback (N : ℕ) [NeZero N]
    (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (v : ℂ) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    let proj : ℍ→LPSOriginalFilledCurve N := fun σ => Sum.inl (Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) σ)
    lpsOriginalFilledDifferential N hN f (proj τ)
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) proj τ v) = lpsCuspDifferential N f τ v := by sorry
