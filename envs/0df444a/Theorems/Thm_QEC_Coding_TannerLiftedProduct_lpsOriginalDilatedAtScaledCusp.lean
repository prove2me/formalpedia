-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDilatedAtScaledCusp
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalDilatedAtScaledCusp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:22:26.032094+00:00
-- url     : https://prove2.me/theorems/1037f9bf-2975-494d-b75d-832fd0897739
-- title:
--   Tanner Lifted Product: lps Original Dilated At Scaled Cusp
-- statement:
--   Actual integral Bezout triangularization at the scaled cusp identifies the transformed original j with an affine slope equal to the squared gcd.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactStabilizer.lean#L138-L225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactStabilizer.lean#L138-L225

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalDilatedAtScaledCusp (N : ℕ) (hN : 0<N) (γ : SL(2,ℤ)) :
    ∃ r : ℝ, ∀ σ : ℍ,
      lpsOriginalJDilated N hN (γ • (lpsE2AffineMatrix N hN 0 • σ))=
        lpsOriginalJInvariant
          (lpsE2AffineMatrix ((Int.gcd ((N:ℤ)*γ 0 0) (γ 1 0))^2)
            (pow_pos (lpsOriginalDilationColumnGcdPos N hN γ) 2) r • σ) := by sorry
