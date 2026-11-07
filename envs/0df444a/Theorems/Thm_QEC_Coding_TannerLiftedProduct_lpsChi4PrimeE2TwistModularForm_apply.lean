-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4PrimeE2TwistModularForm_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4PrimeE2TwistModularForm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:16:58.078545+00:00
-- url     : https://prove2.me/theorems/389b0f86-bca8-4064-84c0-9413569d7787
-- title:
--   Tanner Lifted Product: lps Chi4 Prime E2 Twist Modular Form apply
-- statement:
--   The bundled form retains the genuine quarter-translate function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIteratedEisenstein.lean#L328-L329
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIteratedEisenstein.lean#L328-L329

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsChi4PrimeE2TwistModularForm_apply (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (z : ℍ) :
    lpsChi4PrimeE2TwistModularForm q hq2 z=lpsChi4PrimeE2Twist q z := by sorry
