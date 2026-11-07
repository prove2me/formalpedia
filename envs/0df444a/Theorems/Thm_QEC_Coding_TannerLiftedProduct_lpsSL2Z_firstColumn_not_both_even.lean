-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSL2Z_firstColumn_not_both_even
-- name    : QEC.Coding.TannerLiftedProduct.lpsSL2Z_firstColumn_not_both_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:50:22.547753+00:00
-- url     : https://prove2.me/theorems/040b40b9-dddc-40c5-839d-244d520d85fd
-- title:
--   Tanner Lifted Product: lps SL2 Z first Column not both even
-- statement:
--   Primitivity excludes simultaneous even entries in the genuine first column.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L132-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L132-L137

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsSL2Z_firstColumn_not_both_even (γ : SL(2,ℤ)) :
    ¬((2:ℤ)∣γ 0 0 ∧ (2:ℤ)∣γ 1 0) := by sorry
