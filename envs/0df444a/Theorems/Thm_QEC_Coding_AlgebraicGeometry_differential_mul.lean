-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_differential_mul
-- name    : QEC.Coding.AlgebraicGeometry.differential_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:45:49.557214+00:00
-- url     : https://prove2.me/theorems/0c85bb13-94b9-4b22-a3fd-620ac5f3e583
-- title:
--   Algebraic Geometry: differential mul
-- statement:
--   Leibniz's rule for the actual universal differential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/Differential.lean#L43-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/Differential.lean#L43-L45

import Mathlib.RingTheory.Kaehler.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SeparableDerivationExtension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable (k F : Type*) [Field k] [Field F] [Algebra k F]

theorem QEC.Coding.AlgebraicGeometry.differential_mul (f g : F) :
    differential k F (f * g) = f • differential k F g + g • differential k F f := by sorry
