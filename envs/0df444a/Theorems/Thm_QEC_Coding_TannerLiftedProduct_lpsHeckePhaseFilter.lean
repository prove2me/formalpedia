-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePhaseFilter
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckePhaseFilter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:17:47.571374+00:00
-- url     : https://prove2.me/theorems/8665e36b-fd54-440d-8bb8-b3004ef8d7fa
-- title:
--   Tanner Lifted Product: lps Hecke Phase Filter
-- statement:
--   The genuine finite additive-character sum selects precisely the multiples of p.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCoefficients.lean#L69-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCoefficients.lean#L69-L80

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsHeckePhaseFilter (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (∑ j : Fin p,ZMod.stdAddChar (j.val:ZMod p)^n)=if p∣n then (p:ℂ) else 0 := by sorry
