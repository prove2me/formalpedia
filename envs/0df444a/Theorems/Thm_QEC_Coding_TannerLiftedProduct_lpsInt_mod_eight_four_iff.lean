-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsInt_mod_eight_four_iff
-- name    : QEC.Coding.TannerLiftedProduct.lpsInt_mod_eight_four_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:05:54.233572+00:00
-- url     : https://prove2.me/theorems/6f37b949-22bd-4f3c-bf87-52caa097ddfb
-- title:
--   Tanner Lifted Product: lps Int mod eight four iff
-- statement:
--   The signed remainder-four condition is precisely divisibility by four without divisibility by eight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinDilation.lean#L198-L200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinDilation.lean#L198-L200

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsInt_mod_eight_four_iff (C : ℤ) : C%8=4 ↔ (4:ℤ)∣C ∧ ¬(8:ℤ)∣C := by sorry
