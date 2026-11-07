-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_cusp_cusp_differential
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilled_cusp_cusp_differential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:48:03.286322+00:00
-- url     : https://prove2.me/theorems/91020eb2-833b-405e-8e55-98b8ae8be92e
-- title:
--   Tanner Lifted Product: lps Original Filled cusp cusp differential
-- statement:
--   True cusp overlaps are either identical or empty and satisfy the differential law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialGluing.lean#L120-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialGluing.lean#L120-L146

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialGluing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilled_cusp_cusp_differential (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (c d : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (z : ℂ) (hz : letI := lpsOriginalFilledTopology N
      z∈((lpsOriginalFilledCuspChart N c).symm.trans
        (lpsOriginalFilledCuspChart N d)).source) :
    letI := lpsOriginalFilledTopology N
    let e := (lpsOriginalFilledCuspChart N c).symm.trans (lpsOriginalFilledCuspChart N d)
    lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N d) (e z) *
      deriv e z = lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N c) z := by sorry
