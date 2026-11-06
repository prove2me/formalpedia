-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_differentIdeal_multiplicity_map_algEquiv_eq
-- name    : QEC.Coding.AlgebraicGeometry.differentIdeal_multiplicity_map_algEquiv_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:36:36.463512+00:00
-- url     : https://prove2.me/theorems/3b9446ec-9d21-470e-a568-717f710046b8
-- title:
--   Algebraic Geometry: different Ideal multiplicity map alg Equiv eq
-- statement:
--   Different multiplicities are preserved by an equivalence of integral algebras.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/Transport.lean#L208-L224
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/Transport.lean#L208-L224

import Mathlib.RingTheory.DedekindDomain.Different
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_Transport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
attribute [local instance] FractionRing.liftAlgebra

theorem QEC.Coding.AlgebraicGeometry.differentIdeal_multiplicity_map_algEquiv_eq
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsIntegrallyClosed A]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra A C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    (sigma : B ≃ₐ[A] C) (P : Ideal B) :
    multiplicity (Ideal.map sigma P) (differentIdeal A C) =
      multiplicity P (differentIdeal A B) := by sorry
