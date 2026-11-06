-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_differentIdeal_eq_top_of_algEquiv
-- name    : QEC.Coding.AlgebraicGeometry.differentIdeal_eq_top_of_algEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:51:07.903997+00:00
-- url     : https://prove2.me/theorems/19fbadc1-0e94-4551-92f5-8cd98b650960
-- title:
--   Algebraic Geometry: different Ideal eq top of alg Equiv
-- statement:
--   The Algebraic Geometry construction uses the different Ideal eq top of alg Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/Transport.lean#L170-L181
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/Transport.lean#L170-L181

import Mathlib.RingTheory.DedekindDomain.Different
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_Transport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
attribute [local instance] FractionRing.liftAlgebra

theorem QEC.Coding.AlgebraicGeometry.differentIdeal_eq_top_of_algEquiv
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsIntegrallyClosed A]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra A C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    (σ : B ≃ₐ[A] C)
    (hC : differentIdeal A C = ⊤) :
    differentIdeal A B = ⊤ := by sorry
