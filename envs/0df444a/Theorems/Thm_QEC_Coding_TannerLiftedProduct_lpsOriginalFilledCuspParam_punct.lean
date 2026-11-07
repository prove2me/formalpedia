-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_punct
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspParam_punct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:38:51.082248+00:00
-- url     : https://prove2.me/theorems/6211bb25-8620-471c-bf87-56ab194a11c7
-- title:
--   Tanner Lifted Product: lps Original Filled Cusp Param punct
-- statement:
--   Away from zero the filled parametrization is the actual original inverse punctured coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L295-L303
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L295-L303

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspParam_punct (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (q : lpsOriginalCuspDisk N (lpsOriginalCuspRepresentative N c)) :
    lpsOriginalFilledCuspParam N c
      (lpsOriginalCuspPunctToFull N (lpsOriginalCuspRepresentative N c) q)=
        Sum.inl (lpsOriginalCuspPunctInverse N (lpsOriginalCuspRepresentative N c) q) := by sorry
