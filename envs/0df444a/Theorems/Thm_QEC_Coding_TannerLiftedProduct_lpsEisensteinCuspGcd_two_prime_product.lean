-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEisensteinCuspGcd_two_prime_product
-- name    : QEC.Coding.TannerLiftedProduct.lpsEisensteinCuspGcd_two_prime_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:37:06.688221+00:00
-- url     : https://prove2.me/theorems/50d861e8-c629-472d-a05d-8d61d4c5e1f5
-- title:
--   Tanner Lifted Product: lps Eisenstein Cusp Gcd two prime product
-- statement:
--   The actual denominator gcd factors over coprime powers of two and the residue prime.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCusps.lean#L43-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCusps.lean#L43-L51

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsEisensteinCuspGcd_two_prime_product (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (a b : ℕ) (γ : SL(2,ℤ)) :
    Int.gcd ((2^a*q^b:ℕ):ℤ) (γ 1 0)=
      Int.gcd ((2^a:ℕ):ℤ) (γ 1 0)*Int.gcd ((q^b:ℕ):ℤ) (γ 1 0) := by sorry
