-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleSimplePoleResidueSum_eq_zero_of_mem_differentialFilter
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSimplePoleResidueSum_eq_zero_of_mem_differentialFilter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:40:18.049179+00:00
-- url     : https://prove2.me/theorems/5c1b8e40-66a2-4828-b80e-8126369f1517
-- title:
--   Global Place: global Adele Simple Pole Residue Sum eq zero of mem differential Filter
-- statement:
--   The traced residue sum vanishes on `A((omega))`, because every local
--   product is regular.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleDifferentialResidue.lean#L353-L375
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleDifferentialResidue.lean#L353-L375

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSimplePoleResidueSum_eq_zero_of_mem_differentialFilter
    (omega : Differential k F) (homega : omega ≠ 0)
    (a : globalAdeleFilter (k := k) (F := F)
      (FunctionFieldDifferential.differentialDivisor
        (k := k) (F := F) omega homega)) :
    globalAdeleSimplePoleResidueSum (k := k) (F := F) omega homega
        ⟨a, globalAdeleFilter_le_globalAdeleSimplePoleSubmodule
          (k := k) (F := F) omega homega a.property⟩ = 0 := by sorry
