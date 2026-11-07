-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiPowerSeriesEvalOne_rhs
-- name    : QEC.Coding.TannerLiftedProduct.jacobiPowerSeriesEvalOne_rhs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:26:36.902401+00:00
-- url     : https://prove2.me/theorems/23f11fef-4512-4702-a502-1e24ee72183b
-- title:
--   Tanner Lifted Product: jacobi Power Series Eval One rhs
-- statement:
--   The series side of the bivariate JTP specializes coefficientwise to the
--   rational integer-theta series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductSpecialization.lean#L128-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductSpecialization.lean#L128-L170

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
set_option linter.style.haveILetI false

theorem QEC.Coding.TannerLiftedProduct.jacobiPowerSeriesEvalOne_rhs :
    jacobiPowerSeriesEvalOne JacobiTripleProductCore.rhs =
      rationalIntegerThetaSeries := by sorry
