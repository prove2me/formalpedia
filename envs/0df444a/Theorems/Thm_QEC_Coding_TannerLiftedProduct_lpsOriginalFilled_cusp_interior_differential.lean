-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_cusp_interior_differential
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilled_cusp_interior_differential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:47:43.04941+00:00
-- url     : https://prove2.me/theorems/f08a3ec4-7eaf-4dc5-b70d-cce976ce3bbd
-- title:
--   Tanner Lifted Product: lps Original Filled cusp interior differential
-- statement:
--   The actual cusp-to-interior overlap satisfies the reverse differential law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialGluing.lean#L84-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialGluing.lean#L84-L117

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialGluing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilled_cusp_interior_differential (N : ℕ) [NeZero N]
    (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (z : ℂ) (hz : letI := lpsOriginalFilledTopology N
      z∈((lpsOriginalFilledCuspChart N c).symm.trans
        (lpsOriginalFilledInteriorChart N hN x)).source) :
    letI := lpsOriginalFilledTopology N
    let e := (lpsOriginalFilledCuspChart N c).symm.trans
      (lpsOriginalFilledInteriorChart N hN x)
    f (UpperHalfPlane.ofComplex (e z)) * deriv e z =
      lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N c) z := by sorry
