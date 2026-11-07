-- Prove2me | Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_hasSum_nat_jacobiTheta__real_cc862f55b35d
-- name    : P2M_QEC_Coding_TannerLiftedProduct_hasSum_nat_jacobiTheta__real_cc862f55b35d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:42:09.508402+00:00
-- url     : https://prove2.me/theorems/82d389ca-4c38-4eb8-a5b1-a158f9fb8e78
-- title:
--   P2 M QEC Coding Tanner Lifted Product has Sum nat jacobi Theta  real cc862f55b35d: P2 M QEC Coding Tanner Lifted Product has Sum nat jacobi Theta  real cc862f55b35d
-- statement:
--   Pair the positive and negative terms after removing the constant term.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCharacteristics.lean#L173-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCharacteristics.lean#L173-L179

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real Filter Topology

theorem P2M_QEC_Coding_TannerLiftedProduct_hasSum_nat_jacobiTheta__real_cc862f55b35d (a : ℝ) (z : ℂ) (hz : 0<z.im) :
    HasSum (fun n : ℕ => jacobiTheta₂_term (n+1) (a:ℂ) z +
      jacobiTheta₂_term (-(n+1)) (a:ℂ) z) (jacobiTheta₂ (a:ℂ) z-1) := by sorry

alias «QEC».«Coding».«TannerLiftedProduct».«hasSum_nat_jacobiTheta₂_real» := P2M_QEC_Coding_TannerLiftedProduct_hasSum_nat_jacobiTheta__real_cc862f55b35d
