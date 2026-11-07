-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilatedExactStabilizer
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJDilatedExactStabilizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:20:44.281489+00:00
-- url     : https://prove2.me/theorems/893e2bb1-cc13-4e3c-9f27-2e52239cc0eb
-- title:
--   Tanner Lifted Product: lps Original JDilated Exact Stabilizer
-- statement:
--   The stabilizer of SAME original dilated j under integral SL2 is exactly Gamma0 at every positive, including composite, level.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactStabilizer.lean#L238-L255
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactStabilizer.lean#L238-L255

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJDilatedExactStabilizer (N : ℕ) (hN : 0<N) (γ : SL(2,ℤ)) :
    (∀ τ : ℍ,lpsOriginalJDilated N hN (γ•τ)=lpsOriginalJDilated N hN τ)↔
      γ∈CongruenceSubgroup.Gamma0 N := by sorry
