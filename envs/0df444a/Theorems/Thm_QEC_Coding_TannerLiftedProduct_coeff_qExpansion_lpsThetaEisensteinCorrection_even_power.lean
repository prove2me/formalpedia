-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsThetaEisensteinCorrection_even_power
-- name    : QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsThetaEisensteinCorrection_even_power
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T04:35:58.786816+00:00
-- url     : https://prove2.me/theorems/7ac314d1-1ec4-4eca-870d-4d3f21262172
-- title:
--   Tanner Lifted Product: coeff q Expansion lps Theta Eisenstein Correction even power
-- statement:
--   At every even power of an odd prime-unit index the actual correction coefficient is twice the divisor sum divided by the PSL cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCorrection.lean#L154-L176
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCorrection.lean#L154-L176

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsThetaEisensteinCorrection_even_power (p q : ℕ) [Fact q.Prime]
    (hq2 : q≠2) (hp : Odd p) (hpq : ¬q∣p) (n : ℕ) :
    PowerSeries.coeff (p^(2*n)) (UpperHalfPlane.qExpansion 1 (lpsThetaEisensteinCorrection q hq2))=
      4*(ArithmeticFunction.sigma 1 (p^(2*n)):ℂ)/((q:ℂ)*((q:ℂ)^2-1)) := by sorry
