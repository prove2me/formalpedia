-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPrimeCuspShift_unit
-- name    : QEC.Coding.TannerLiftedProduct.lpsPrimeCuspShift_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:49:46.902244+00:00
-- url     : https://prove2.me/theorems/2eb99a98-93eb-40f0-bcc3-7a5eb648984a
-- title:
--   Tanner Lifted Product: lps Prime Cusp Shift unit
-- statement:
--   A nonzero canonical prime-modulus residue is coprime to the modulus squared.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L210-L219
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L210-L219

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsPrimeCuspShift_unit (q : ℕ) [Fact q.Prime] (r : Fin q) (hr : r≠0) :
    r.val.Coprime (q^2) := by sorry
