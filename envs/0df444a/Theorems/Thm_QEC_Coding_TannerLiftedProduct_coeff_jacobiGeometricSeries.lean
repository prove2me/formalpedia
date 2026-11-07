-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiGeometricSeries
-- name    : QEC.Coding.TannerLiftedProduct.coeff_jacobiGeometricSeries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:18:09.21921+00:00
-- url     : https://prove2.me/theorems/c6982afd-3b41-4e0d-988a-4e464a4253ea
-- title:
--   Tanner Lifted Product: coeff jacobi Geometric Series
-- statement:
--   The Tanner Lifted Product construction uses the coeff jacobi Geometric Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L21-L23
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L21-L23

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.coeff_jacobiGeometricSeries (n : ℕ) :
    PowerSeries.coeff n jacobiGeometricSeries = 1 := by sorry
