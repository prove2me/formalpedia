-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_continuous_jacobiPowerSeriesEvalOne
-- name    : QEC.Coding.TannerLiftedProduct.continuous_jacobiPowerSeriesEvalOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:26:17.912471+00:00
-- url     : https://prove2.me/theorems/f16676cf-7672-41a0-9021-806a6dba360f
-- title:
--   Tanner Lifted Product: continuous jacobi Power Series Eval One
-- statement:
--   The Tanner Lifted Product construction uses the continuous jacobi Power Series Eval One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductSpecialization.lean#L38-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductSpecialization.lean#L38-L56

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
set_option linter.style.haveILetI false

theorem QEC.Coding.TannerLiftedProduct.continuous_jacobiPowerSeriesEvalOne :
    letI := JacobiTripleProductCore.piTop
    Continuous jacobiPowerSeriesEvalOne := by sorry
