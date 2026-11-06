-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_differentIdeal_map_algEquiv_eq
-- name    : QEC.Coding.AlgebraicGeometry.differentIdeal_map_algEquiv_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:23:01.173137+00:00
-- url     : https://prove2.me/theorems/c441db63-28c9-453f-aa40-e87d11bd6e38
-- title:
--   Algebraic Geometry: different Ideal map alg Equiv eq
-- statement:
--   The trace-defined different ideal is transported by an algebra
--   equivalence between integral carriers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/Transport.lean#L137-L166
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/Transport.lean#L137-L166

import Mathlib.RingTheory.DedekindDomain.Different
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_Transport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
attribute [local instance] FractionRing.liftAlgebra

theorem QEC.Coding.AlgebraicGeometry.differentIdeal_map_algEquiv_eq
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsIntegrallyClosed A]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra A C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    (sigma : B ≃ₐ[A] C) :
    Ideal.map sigma (differentIdeal A B) = differentIdeal A C := by sorry
