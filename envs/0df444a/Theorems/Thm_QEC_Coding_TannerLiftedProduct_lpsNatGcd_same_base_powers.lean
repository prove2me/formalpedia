-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatGcd_same_base_powers
-- name    : QEC.Coding.TannerLiftedProduct.lpsNatGcd_same_base_powers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:38:24.764829+00:00
-- url     : https://prove2.me/theorems/d93c6a48-e71c-47d2-aa10-cc3f4a56c299
-- title:
--   Tanner Lifted Product: lps Nat Gcd same base powers
-- statement:
--   Comparable powers have exactly the smaller power as their gcd.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L79-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L79-L84

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsNatGcd_same_base_powers (p a t : ℕ) : Nat.gcd (p^a) (p^t)=p^(min a t) := by sorry
