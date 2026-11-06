-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleQuotientRank_eq_indexOfSpecialty
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleQuotientRank_eq_indexOfSpecialty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:13:33.064194+00:00
-- url     : https://prove2.me/theorems/e3683dbf-c85a-4c77-919c-5dabf083af5f
-- title:
--   Global Place: global Adele Quotient Rank eq index Of Specialty
-- statement:
--   The rank of the actual intrinsic adele quotient is the Riemann--Roch
--   index of specialty.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleQuotient.lean#L175-L227
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleQuotient.lean#L175-L227

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleSandwich
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleQuotient
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleQuotientAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleQuotientScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable [IsFullConstantField k F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleQuotientFilterAddCommGroup
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleQuotientFilterModule

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleQuotientRank_eq_indexOfSpecialty
    (D : Divisor (GlobalPlace k F)) :
    globalAdeleQuotientRank (k := k) (F := F) D =
      riemannRochIndexOfSpecialty
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D := by sorry
