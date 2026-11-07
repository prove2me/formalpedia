-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_interior_preimage
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspParam_interior_preimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:42:33.925239+00:00
-- url     : https://prove2.me/theorems/e25591bb-5ca2-41b3-a8e4-560068993100
-- title:
--   Tanner Lifted Product: lps Original Filled Cusp Param interior preimage
-- statement:
--   True disc preimages of original interior images are exactly the punctured inverse preimages.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L370-L394
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L370-L394

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspParam_interior_preimage (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (s : Set (MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)) :
    lpsOriginalFilledCuspParam N c ⁻¹' (Sum.inl '' s)=
      lpsOriginalCuspPunctToFull N (lpsOriginalCuspRepresentative N c) ''
        (lpsOriginalCuspPunctInverse N (lpsOriginalCuspRepresentative N c) ⁻¹' s) := by sorry
