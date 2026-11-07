-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaEisensteinCorrectionCoefficient_of_unit_characters
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinCorrectionCoefficient_of_unit_characters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:07:51.670336+00:00
-- url     : https://prove2.me/theorems/1690a46e-9396-4029-b98c-588eaa0c7830
-- title:
--   Tanner Lifted Product: lps Theta Eisenstein Correction Coefficient of unit characters
-- statement:
--   At odd prime-unit indices with unit character values the complete coefficient is four times the divisor sum over the group normalization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCorrection.lean#L113-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCorrection.lean#L113-L151

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinCorrectionCoefficient_of_unit_characters (q : ℕ) [Fact q.Prime]
    (n : ℕ) (h2 : ¬2∣n) (hq : ¬q∣n)
    (hc4 : lpsChi4E2Character (n:ZMod 4)=1)
    (hcq : lpsQuadraticE2Character q (n:ZMod q)=1) :
    lpsThetaEisensteinCorrectionCoefficient q n=
      4*(ArithmeticFunction.sigma 1 n:ℂ)/((q:ℂ)*((q:ℂ)^2-1)) := by sorry
