-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_dvrParameterLocalMap_isLocalHom
-- name    : QEC.Coding.AlgebraicGeometry.dvrParameterLocalMap_isLocalHom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:56:32.322282+00:00
-- url     : https://prove2.me/theorems/2fed496f-17d8-4bf9-b896-a08198b88613
-- title:
--   Algebraic Geometry: dvr Parameter Local Map is Local Hom
-- statement:
--   The Algebraic Geometry construction uses the dvr Parameter Local Map is Local Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/CharZeroCurveSmoothness.lean#L112-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/CharZeroCurveSmoothness.lean#L112-L130

import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_CharZeroCurveSmoothness
set_option autoImplicit false
open scoped TensorProduct
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (k V : Type*) [Field k] [CommRing V] [IsDomain V] [Algebra k V]
    (π : V)
attribute [local instance] QEC.Coding.AlgebraicGeometry.dvrParameterPrime_isPrime
omit [IsDomain V]

theorem QEC.Coding.AlgebraicGeometry.dvrParameterLocalMap_isLocalHom [IsLocalRing V] :
    IsLocalHom (dvrParameterLocalMap k V π).toRingHom := by sorry
