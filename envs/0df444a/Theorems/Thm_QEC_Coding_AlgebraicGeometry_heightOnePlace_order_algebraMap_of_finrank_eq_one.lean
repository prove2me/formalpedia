-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_heightOnePlace_order_algebraMap_of_finrank_eq_one
-- name    : QEC.Coding.AlgebraicGeometry.heightOnePlace_order_algebraMap_of_finrank_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:50:40.420355+00:00
-- url     : https://prove2.me/theorems/aa7240ea-f0e3-4649-a2eb-d91ff85c30d4
-- title:
--   Algebraic Geometry: height One Place order algebra Map of finrank eq one
-- statement:
--   Orders agree under the actual inclusion in a degree-one field step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/TrivialFieldExtension.lean#L67-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/TrivialFieldExtension.lean#L67-L79

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

theorem QEC.Coding.AlgebraicGeometry.heightOnePlace_order_algebraMap_of_finrank_eq_one
    {k : Type*} [Field k] [Finite k] [Algebra k K] [Algebra k L]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (Q : IsDedekindDomain.HeightOneSpectrum C) [Q.asIdeal.LiesOver H.asIdeal]
    (hdegree : Module.finrank K L = 1) (x : K) :
    (heightOnePlace (k := k) (K := L) Q).order (algebraMap K L x) =
      (heightOnePlace (k := k) (K := K) H).order x := by sorry
