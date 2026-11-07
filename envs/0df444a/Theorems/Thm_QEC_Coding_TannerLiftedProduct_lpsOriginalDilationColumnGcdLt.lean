-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDilationColumnGcdLt
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalDilationColumnGcdLt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:22:02.194211+00:00
-- url     : https://prove2.me/theorems/953aaaaa-8580-4d8b-9942-e8f2c4e0d550
-- title:
--   Tanner Lifted Product: lps Original Dilation Column Gcd Lt
-- statement:
--   If the lower-left entry is not divisible by the level, the actual first-column gcd is strictly smaller.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactStabilizer.lean#L113-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactStabilizer.lean#L113-L121

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalDilationColumnGcdLt (N : ℕ) (hN : 0<N)
    (γ : SL(2,ℤ)) (hc : ¬(N:ℤ)∣γ 1 0) :
    Int.gcd ((N:ℤ)*γ 0 0) (γ 1 0)<N := by sorry
