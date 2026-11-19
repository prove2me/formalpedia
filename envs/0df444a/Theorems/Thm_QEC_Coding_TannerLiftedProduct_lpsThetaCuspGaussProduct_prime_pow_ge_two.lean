-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_prime_pow_ge_two
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_prime_pow_ge_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:35:47.90963+00:00
-- url     : https://prove2.me/theorems/da4ac74a-5c2b-4276-b06d-c8392d1d94b9
-- title:
--   Tanner Lifted Product: lps Theta Cusp Gauss Product prime pow ge two
-- statement:
--   At higher residue-prime powers the actual theta product is prime cubed times modulus squared.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspLocalFactors.lean#L114-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspLocalFactors.lean#L114-L127

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_prime_pow_ge_two (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (e : ℕ) (a : ℤ) (ha : IsUnit (a:ZMod (q^(e+2)))) :
    lpsThetaCuspGaussProduct q a (q^(e+2))=(q:ℂ)^3*((q^(e+2):ℕ):ℂ)^2 := by sorry
