-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaEisensteinChi4Weight_scaled
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinChi4Weight_scaled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:37:01.136988+00:00
-- url     : https://prove2.me/theorems/b9a69857-8bc6-4be8-a898-537dc0601b88
-- title:
--   Tanner Lifted Product: lps Theta Eisenstein Chi4 Weight scaled
-- statement:
--   The genuine character-four weights and dilation factors reproduce the negative prime-power weights.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCusps.lean#L74-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCusps.lean#L74-L80

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinChi4Weight_scaled (q : ℕ) [Fact q.Prime] (b : Fin 3) :
    lpsThetaEisensteinChi4Weight q b/((q^b.val:ℕ):ℂ)^2=
      -lpsThetaEisensteinPrimeWeight q b/((q^b.val:ℕ):ℂ) := by sorry
