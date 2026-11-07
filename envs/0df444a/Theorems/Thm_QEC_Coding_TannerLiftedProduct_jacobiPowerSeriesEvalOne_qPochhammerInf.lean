-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiPowerSeriesEvalOne_qPochhammerInf
-- name    : QEC.Coding.TannerLiftedProduct.jacobiPowerSeriesEvalOne_qPochhammerInf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:26:27.080244+00:00
-- url     : https://prove2.me/theorems/c930246f-4964-4d01-9b1f-cfcff3023098
-- title:
--   Tanner Lifted Product: jacobi Power Series Eval One q Pochhammer Inf
-- statement:
--   Mapping a specialized q-Pochhammer product through evaluation at the
--   Laurent variable `1` commutes with its convergent infinite product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductSpecialization.lean#L66-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductSpecialization.lean#L66-L86

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
set_option linter.style.haveILetI false

theorem QEC.Coding.TannerLiftedProduct.jacobiPowerSeriesEvalOne_qPochhammerInf
    (A : JacobiTripleProductCore.R) :
    letI := JacobiTripleProductCore.piTop
    Multipliable (fun n : ℕ =>
        1 - A * (JacobiTripleProductCore.q ^ 2) ^ n) →
    jacobiPowerSeriesEvalOne
        (JacobiTripleProductCore.qPochhammerInf A
          (JacobiTripleProductCore.q ^ 2)) =
      (∏' n : ℕ,
        ((1 : ℚ⟦X⟧) - jacobiPowerSeriesEvalOne A *
          PowerSeries.X ^ (2 * n))) := by sorry
