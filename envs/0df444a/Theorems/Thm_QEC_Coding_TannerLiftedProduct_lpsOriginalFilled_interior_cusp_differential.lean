-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_interior_cusp_differential
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilled_interior_cusp_differential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:47:14.192323+00:00
-- url     : https://prove2.me/theorems/d69a720b-a1d0-4a39-8d5f-b4461cd80810
-- title:
--   Tanner Lifted Product: lps Original Filled interior cusp differential
-- statement:
--   The actual interior-to-cusp overlap satisfies the derivative-weighted differential law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialGluing.lean#L45-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialGluing.lean#L45-L81

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialGluing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilled_interior_cusp_differential (N : ℕ) [NeZero N]
    (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (z : ℂ) (hz : letI := lpsOriginalFilledTopology N
      z∈((lpsOriginalFilledInteriorChart N hN x).symm.trans
        (lpsOriginalFilledCuspChart N c)).source) :
    letI := lpsOriginalFilledTopology N
    let e := (lpsOriginalFilledInteriorChart N hN x).symm.trans
      (lpsOriginalFilledCuspChart N c)
    lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N c) (e z) *
      deriv e z = f (UpperHalfPlane.ofComplex z) := by sorry
