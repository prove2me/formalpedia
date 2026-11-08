-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiThetaProduct_eq_rationalIntegerThetaSeries
-- name    : QEC.Coding.TannerLiftedProduct.jacobiThetaProduct_eq_rationalIntegerThetaSeries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:57:12.431209+00:00
-- url     : https://prove2.me/theorems/f13f474a-f137-4f90-a549-a65a17c8e4d9
-- title:
--   Tanner Lifted Product: jacobi Theta Product eq rational Integer Theta Series
-- statement:
--   Jacobi's theta product identity over rational formal power series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductSpecialization.lean#L173-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductSpecialization.lean#L173-L182

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
set_option linter.style.haveILetI false

theorem QEC.Coding.TannerLiftedProduct.jacobiThetaProduct_eq_rationalIntegerThetaSeries :
    jacobiThetaProduct = rationalIntegerThetaSeries := by sorry
