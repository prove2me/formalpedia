-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiLambertTerm_eq_geometric
-- name    : QEC.Coding.TannerLiftedProduct.jacobiLambertTerm_eq_geometric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:53:32.941696+00:00
-- url     : https://prove2.me/theorems/2eed43e6-b0a8-455b-ad4d-8ff95cd22ff8
-- title:
--   Tanner Lifted Product: jacobi Lambert Term eq geometric
-- statement:
--   For positive `d`, the coefficientwise Lambert summand is the familiar
--   formal fraction `d * (X^d + X^(2d) + ⋯)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L325-L335
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L325-L335

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.jacobiLambertTerm_eq_geometric {d : ℕ} (hd : d ≠ 0) :
    jacobiLambertTerm d =
      PowerSeries.C (d : ℚ) *
        ((jacobiGeometricSeries.subst (PowerSeries.X ^ d)) - 1) := by sorry
