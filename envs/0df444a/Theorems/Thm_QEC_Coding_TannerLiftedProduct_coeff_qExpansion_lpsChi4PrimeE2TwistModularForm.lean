-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsChi4PrimeE2TwistModularForm
-- name    : QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsChi4PrimeE2TwistModularForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:13:55.545371+00:00
-- url     : https://prove2.me/theorems/aa7a26f9-4213-41d7-8599-ec04ba6ffae9
-- title:
--   Tanner Lifted Product: coeff q Expansion lps Chi4 Prime E2 Twist Modular Form
-- statement:
--   The genuine modular form keeps every actual coefficient with both character factors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIteratedEisenstein.lean#L332-L335
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIteratedEisenstein.lean#L332-L335

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsChi4PrimeE2TwistModularForm (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsChi4PrimeE2TwistModularForm q hq2))=
      -24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsQuadraticE2Character q (n:ZMod q)*lpsChi4E2Character (n:ZMod 4) := by sorry
