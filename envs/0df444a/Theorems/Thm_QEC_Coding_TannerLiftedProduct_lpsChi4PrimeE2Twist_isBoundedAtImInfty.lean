-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4PrimeE2Twist_isBoundedAtImInfty
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4PrimeE2Twist_isBoundedAtImInfty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:13:29.918998+00:00
-- url     : https://prove2.me/theorems/7a96bcb8-c06e-43e1-a93b-fdef43e939af
-- title:
--   Tanner Lifted Product: lps Chi4 Prime E2 Twist is Bounded At Im Infty
-- statement:
--   The actual convergent iterated series proves boundedness in the full infinity filter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIteratedEisenstein.lean#L134-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIteratedEisenstein.lean#L134-L138

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsChi4PrimeE2Twist_isBoundedAtImInfty (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    UpperHalfPlane.IsBoundedAtImInfty (lpsChi4PrimeE2Twist q) := by sorry
