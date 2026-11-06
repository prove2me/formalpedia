-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleWeilDifferentialOfDifferential_toFun_of_mem_simplePole
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleWeilDifferentialOfDifferential_toFun_of_mem_simplePole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:48:15.776687+00:00
-- url     : https://prove2.me/theorems/52698f1e-6a62-4105-aad4-b38816ad5e1b
-- title:
--   Global Place: global Adele Weil Differential Of Differential to Fun of mem simple Pole
-- statement:
--   The extended functional agrees with the traced residue sum on every
--   intrinsic simple-pole adele.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleDifferentialWeil.lean#L198-L207
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleDifferentialWeil.lean#L198-L207

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialWeil
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleDifferentialWeilAlgebra
attribute [local instance] globalAdeleDifferentialWeilAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleDifferentialWeilScalarTower
attribute [local instance] globalAdeleDifferentialWeilScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable [IsFullConstantField k F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleWeilDifferentialOfDifferential_toFun_of_mem_simplePole
    (omega : Differential k F) (homega : omega ≠ 0)
    (a : GlobalAdele (k := k) (F := F))
    (ha : a ∈ globalAdeleSimplePoleSubmodule (k := k) (F := F) omega) :
    (globalAdeleWeilDifferentialOfDifferential
      (k := k) (F := F) omega homega).toFun a =
      globalAdeleSimplePoleResidueSum (k := k) (F := F) omega homega
        ⟨a, ha⟩ := by sorry
