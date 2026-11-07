-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAffinePolePullback
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAffinePolePullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:17:20.344207+00:00
-- url     : https://prove2.me/theorems/25b6455c-1ccf-4f80-811a-f7e905e4dc10
-- title:
--   Tanner Lifted Product: lps Original Affine Pole Pullback
-- statement:
--   Actual pole-weighted affine pullback equals the SAME original analytic K times the remaining nome power.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactStabilizer.lean#L52-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactStabilizer.lean#L52-L65

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAffinePolePullback (m k : ℕ) (hm : 0<m)
    (hmk : m≤k) (r : ℝ) (τ : ℍ) :
    Function.Periodic.qParam 1 (τ:ℂ)^k*
      lpsOriginalJInvariant (lpsE2AffineMatrix m hm r • τ)=
        Function.Periodic.qParam 1 (τ:ℂ)^(k-m)/Function.Periodic.qParam 1 (r:ℂ)*
          lpsOriginalJQCoefficient
            (Function.Periodic.qParam 1 ((lpsE2AffineMatrix m hm r • τ:ℍ):ℂ)) := by sorry
