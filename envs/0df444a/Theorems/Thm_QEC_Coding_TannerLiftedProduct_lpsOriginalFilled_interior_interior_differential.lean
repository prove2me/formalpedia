-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_interior_interior_differential
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilled_interior_interior_differential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:47:13.294862+00:00
-- url     : https://prove2.me/theorems/b612b151-270f-413e-801c-2ef9e54276ea
-- title:
--   Tanner Lifted Product: lps Original Filled interior interior differential
-- statement:
--   True original quotient interior overlaps preserve the original differential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialGluing.lean#L149-L195
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialGluing.lean#L149-L195

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialGluing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilled_interior_interior_differential (N : ℕ) [NeZero N]
    (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (x y : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (z : ℂ) (hz : letI := lpsOriginalFilledTopology N
      z∈((lpsOriginalFilledInteriorChart N hN x).symm.trans
        (lpsOriginalFilledInteriorChart N hN y)).source) :
    letI := lpsOriginalFilledTopology N
    let e := (lpsOriginalFilledInteriorChart N hN x).symm.trans
      (lpsOriginalFilledInteriorChart N hN y)
    f (UpperHalfPlane.ofComplex (e z)) * deriv e z = f (UpperHalfPlane.ofComplex z) := by sorry
