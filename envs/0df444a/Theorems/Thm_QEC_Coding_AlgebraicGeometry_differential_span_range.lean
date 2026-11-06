-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_differential_span_range
-- name    : QEC.Coding.AlgebraicGeometry.differential_span_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:15:17.634288+00:00
-- url     : https://prove2.me/theorems/56ec1819-2301-4237-867a-0587521b9d9f
-- title:
--   Algebraic Geometry: differential span range
-- statement:
--   Universal differentials span the actual Kähler differential module.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/Differential.lean#L53-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/Differential.lean#L53-L56

import Mathlib.RingTheory.Kaehler.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SeparableDerivationExtension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable (k F : Type*) [Field k] [Field F] [Algebra k F]

theorem QEC.Coding.AlgebraicGeometry.differential_span_range :
    Submodule.span F (Set.range (differential k F)) = ⊤ := by sorry
