-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ramificationIdx_and_weakDifferent_of_finrank_eq_one
-- name    : QEC.Coding.AlgebraicGeometry.ramificationIdx_and_weakDifferent_of_finrank_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:28:41.960192+00:00
-- url     : https://prove2.me/theorems/82c1c764-fdda-4841-98ab-ae8abd675a39
-- title:
--   Algebraic Geometry: ramification Idx and weak Different of finrank eq one
-- statement:
--   Both invariants of a redundant field step at the supplied upper prime.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/TrivialFieldExtension.lean#L41-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/TrivialFieldExtension.lean#L41-L63

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

theorem QEC.Coding.AlgebraicGeometry.ramificationIdx_and_weakDifferent_of_finrank_eq_one
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (Q : IsDedekindDomain.HeightOneSpectrum C) [Q.asIdeal.LiesOver H.asIdeal]
    (hdegree : Module.finrank K L = 1) :
    H.asIdeal.ramificationIdx' Q.asIdeal = 1 ∧
      multiplicity Q.asIdeal (differentIdeal B C) =
        2 * (H.asIdeal.ramificationIdx' Q.asIdeal - 1) := by sorry
