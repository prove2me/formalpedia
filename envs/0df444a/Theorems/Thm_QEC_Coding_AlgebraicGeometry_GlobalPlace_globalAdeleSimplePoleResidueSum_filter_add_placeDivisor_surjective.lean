-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleSimplePoleResidueSum_filter_add_placeDivisor_surjective
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSimplePoleResidueSum_filter_add_placeDivisor_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:38:52.201759+00:00
-- url     : https://prove2.me/theorems/150e3f2e-a1df-432a-aa4f-26f83f0121ef
-- title:
--   Global Place: global Adele Simple Pole Residue Sum filter add place Divisor surjective
-- statement:
--   On the one-place enlargement of the divisor of a nonzero differential,
--   the traced residue sum assumes every constant-field value.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleDifferentialResidue.lean#L405-L550
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleDifferentialResidue.lean#L405-L550

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSimplePoleResidueSum_filter_add_placeDivisor_surjective
    (omega : Differential k F) (homega : omega ≠ 0)
    (P : GlobalPlace k F) :
    Function.Surjective fun a : globalAdeleFilter (k := k) (F := F)
        (FunctionFieldDifferential.differentialDivisor
          (k := k) (F := F) omega homega + placeDivisor P) =>
      globalAdeleSimplePoleResidueSum (k := k) (F := F) omega homega
        ⟨(a : GlobalAdele (k := k) (F := F)),
          globalAdeleFilter_add_placeDivisor_le_globalAdeleSimplePoleSubmodule
            (k := k) (F := F) omega homega P a.property⟩ := by sorry
