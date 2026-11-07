-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_nonzero_lift
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspParam_nonzero_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:38:38.176748+00:00
-- url     : https://prove2.me/theorems/a07aec59-9bce-4cc3-a1d0-0b9d535a3183
-- title:
--   Tanner Lifted Product: lps Original Filled Cusp Param nonzero lift
-- statement:
--   Every nonzero true filled coordinate lifts to an actual high original projection with its q formula.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L411-L435
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L411-L435

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspParam_nonzero_lift (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (q : (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)
    (hz : q.val≠0) :
    ∃ τ : {τ : ℍ // 1<τ.im},
      lpsOriginalFilledCuspParam N c q=
        Sum.inl (lpsOriginalCuspProjection N (lpsOriginalCuspRepresentative N c) τ) ∧
      q.val=Function.Periodic.qParam
        (lpsOriginalCuspGroup N (lpsOriginalCuspRepresentative N c)).strictWidthInfty τ.val := by sorry
