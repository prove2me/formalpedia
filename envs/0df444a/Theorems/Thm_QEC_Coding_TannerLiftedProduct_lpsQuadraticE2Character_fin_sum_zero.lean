-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Character_fin_sum_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Character_fin_sum_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:50:01.434135+00:00
-- url     : https://prove2.me/theorems/3f51015e-75d8-4b40-94b8-9aea9efd120e
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Character fin sum zero
-- statement:
--   The actual quadratic character has zero total over the canonical finite residues.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L248-L254
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L248-L254

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Character_fin_sum_zero (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    (∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q))=0 := by sorry
