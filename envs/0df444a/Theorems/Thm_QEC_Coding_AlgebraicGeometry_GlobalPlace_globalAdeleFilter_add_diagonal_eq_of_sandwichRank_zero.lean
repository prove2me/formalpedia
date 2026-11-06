-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleFilter_add_diagonal_eq_of_sandwichRank_zero
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleFilter_add_diagonal_eq_of_sandwichRank_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:13:15.020306+00:00
-- url     : https://prove2.me/theorems/ae4ae45e-7c80-41f6-aa44-ca43391f362b
-- title:
--   Global Place: global Adele Filter add diagonal eq of sandwich Rank zero
-- statement:
--   Vanishing sandwich rank forces the two diagonal-augmented filtration
--   pieces to coincide.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleSandwich.lean#L446-L536
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleSandwich.lean#L446-L536

import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Isomorphisms
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleEffectiveIncrement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Genus
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleSandwich
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Filter
open scoped Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleSandwichAlgebra
attribute [local instance] globalAdeleSandwichAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleSandwichScalarTower
attribute [local instance] globalAdeleSandwichScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable [IsFullConstantField k F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSandwichRiemannRochFiniteDimensional
attribute [local instance] globalAdeleSandwichRiemannRochFiniteDimensional
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSandwichFilterAddCommGroup
attribute [local instance] globalAdeleSandwichFilterAddCommGroup
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSandwichFilterModule
attribute [local instance] globalAdeleSandwichFilterModule

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleFilter_add_diagonal_eq_of_sandwichRank_zero
    {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E)
    (hzero : globalAdeleSandwichRank (k := k) (F := F) D E hDE = 0) :
    globalAdeleFilter (k := k) (F := F) E +
        diagonalAdeleSubmodule (k := k) (F := F) =
      globalAdeleFilter (k := k) (F := F) D +
        diagonalAdeleSubmodule (k := k) (F := F) := by sorry
