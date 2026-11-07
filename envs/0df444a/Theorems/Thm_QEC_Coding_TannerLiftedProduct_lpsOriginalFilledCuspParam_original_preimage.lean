-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_original_preimage
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspParam_original_preimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:42:36.62928+00:00
-- url     : https://prove2.me/theorems/66fb7d10-5964-4869-9694-04a435b34de5
-- title:
--   Tanner Lifted Product: lps Original Filled Cusp Param original preimage
-- statement:
--   Original preimages of a genuine filled-disc image are computed by the true punctured inverse.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L330-L352
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L330-L352

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspParam_original_preimage (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (s : Set ((lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)) :
    (Sum.inl : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → LPSOriginalFilledCurve N) ⁻¹'
      (lpsOriginalFilledCuspParam N c '' s)=
        lpsOriginalCuspPunctInverse N (lpsOriginalCuspRepresentative N c) ''
          (lpsOriginalCuspPunctToFull N (lpsOriginalCuspRepresentative N c) ⁻¹' s) := by sorry
