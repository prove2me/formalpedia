-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_unitMulUniformizerLogDifferentialClass_eq
-- name    : QEC.Coding.AlgebraicGeometry.Differential.unitMulUniformizerLogDifferentialClass_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:16:42.907963+00:00
-- url     : https://prove2.me/theorems/68019612-3e74-4a61-9b5d-4f1ead9f1f08
-- title:
--   Differential: unit Mul Uniformizer Log Differential Class eq
-- statement:
--   Multiplication of the uniformizer by a valuation-ring unit does not change
--   its logarithmic-differential class modulo regular differentials.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/LocalLogarithmicDifferential.lean#L114-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/LocalLogarithmicDifferential.lean#L114-L136

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalLogarithmicDifferential
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

theorem QEC.Coding.AlgebraicGeometry.Differential.unitMulUniformizerLogDifferentialClass_eq
    (P : GlobalPlace k F) (u : P.valuationRingˣ) :
    Submodule.Quotient.mk
        (unitMulUniformizerLogDifferential (k := k) (F := F) P u) =
      uniformizerLogDifferentialClass (k := k) (F := F) P := by sorry
