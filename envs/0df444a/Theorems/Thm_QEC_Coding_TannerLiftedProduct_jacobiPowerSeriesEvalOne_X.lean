-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiPowerSeriesEvalOne_X
-- name    : QEC.Coding.TannerLiftedProduct.jacobiPowerSeriesEvalOne_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:21:01.858271+00:00
-- url     : https://prove2.me/theorems/4238fd4d-5e7f-493d-ac64-5ae8385a0f2f
-- title:
--   Tanner Lifted Product: jacobi Power Series Eval One X
-- statement:
--   The Tanner Lifted Product construction uses the jacobi Power Series Eval One X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductSpecialization.lean#L34-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductSpecialization.lean#L34-L36

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
set_option linter.style.haveILetI false

theorem QEC.Coding.TannerLiftedProduct.jacobiPowerSeriesEvalOne_X :
    jacobiPowerSeriesEvalOne JacobiTripleProductCore.q = PowerSeries.X := by sorry
