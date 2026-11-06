-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_differentIdeal_eq_top_of_finrank_eq_one
-- name    : QEC.Coding.AlgebraicGeometry.differentIdeal_eq_top_of_finrank_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:36:44.17812+00:00
-- url     : https://prove2.me/theorems/c8650669-91f8-4aa0-9ad4-60c41494ed7f
-- title:
--   Algebraic Geometry: different Ideal eq top of finrank eq one
-- statement:
--   A degree-one fraction-field extension has unit different on its actual
--   integral carrier; the proof uses the minimal polynomial of zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/TrivialFieldExtension.lean#L26-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/TrivialFieldExtension.lean#L26-L37

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
import Mathlib.RingTheory.DedekindDomain.Different
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_TrivialFieldExtension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (B C K L : Type*) [CommRing B] [CommRing C] [Field K] [Field L]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [Algebra B C] [Algebra C L] [IsFractionRing C L] [IsScalarTower B C L]
    [Module.IsTorsionFree B C] [Module.Finite B C]
    [Algebra.IsSeparable K L]
include K L

theorem QEC.Coding.AlgebraicGeometry.differentIdeal_eq_top_of_finrank_eq_one
    (hdegree : Module.finrank K L = 1) : differentIdeal B C = ⊤ := by sorry
