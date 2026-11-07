-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiPowerSeriesEvalOne_lhs
-- name    : QEC.Coding.TannerLiftedProduct.jacobiPowerSeriesEvalOne_lhs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:26:39.7228+00:00
-- url     : https://prove2.me/theorems/4f45a51d-378b-4e61-b1ad-9d974b9b87c1
-- title:
--   Tanner Lifted Product: jacobi Power Series Eval One lhs
-- statement:
--   The product side of the bivariate JTP specializes to the rational
--   integer-theta product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductSpecialization.lean#L90-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductSpecialization.lean#L90-L124

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
set_option linter.style.haveILetI false

theorem QEC.Coding.TannerLiftedProduct.jacobiPowerSeriesEvalOne_lhs :
    jacobiPowerSeriesEvalOne JacobiTripleProductCore.lhs =
      jacobiThetaProduct := by sorry
