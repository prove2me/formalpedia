-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleSimplePoleResidueSum_diagonal_eq_zero
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSimplePoleResidueSum_diagonal_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:39:55.704293+00:00
-- url     : https://prove2.me/theorems/c0f848fd-da9c-4a0e-8c1e-e44d02b640f7
-- title:
--   Global Place: global Adele Simple Pole Residue Sum diagonal eq zero
-- statement:
--   A diagonal element in the simple-pole adele submodule has residue sum
--   zero by the global residue theorem for the corresponding global
--   differential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleDifferentialResidue.lean#L380-L401
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleDifferentialResidue.lean#L380-L401

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_FunctionFieldGlobalResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleWeilDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialResidue
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Filter
open scoped BigOperators Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleDifferentialResidueAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleDifferentialResidueScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable [IsFullConstantField k F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSimplePoleResidueSum_diagonal_eq_zero
    (omega : Differential k F) (homega : omega ≠ 0) (f : F)
    (hf : diagonalAdele (k := k) (F := F) f ∈
      globalAdeleSimplePoleSubmodule (k := k) (F := F) omega) :
    globalAdeleSimplePoleResidueSum (k := k) (F := F) omega homega
        ⟨diagonalAdele (k := k) (F := F) f, hf⟩ = 0 := by sorry
