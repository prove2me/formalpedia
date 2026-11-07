-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Character_values
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4E2Character_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:12:27.626271+00:00
-- url     : https://prove2.me/theorems/bc9f6dfb-33cb-4567-938c-3c72a23c0663
-- title:
--   Tanner Lifted Product: lps Chi4 E2 Character values
-- statement:
--   All four actual values include zero at both nonunits and opposite signs on the units.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L37-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L37-L39

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsChi4E2Character_values : lpsChi4E2Character 0=0 ∧ lpsChi4E2Character 1=1 ∧
    lpsChi4E2Character 2=0 ∧ lpsChi4E2Character 3= -1 := by sorry
