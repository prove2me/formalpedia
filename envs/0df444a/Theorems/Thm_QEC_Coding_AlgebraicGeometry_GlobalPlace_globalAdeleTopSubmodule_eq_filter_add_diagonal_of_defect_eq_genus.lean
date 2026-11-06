-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleTopSubmodule_eq_filter_add_diagonal_of_defect_eq_genus
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleTopSubmodule_eq_filter_add_diagonal_of_defect_eq_genus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:11:22.025646+00:00
-- url     : https://prove2.me/theorems/ffaf0ab4-6af6-4c15-b5a2-b0057cb07bc9
-- title:
--   Global Place: global Adele Top Submodule eq filter add diagonal of defect eq genus
-- statement:
--   A genus-attaining divisor saturates the intrinsic adele space after the
--   diagonal function field is adjoined.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleSandwich.lean#L552-L579
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleSandwich.lean#L552-L579

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleTopSubmodule_eq_filter_add_diagonal_of_defect_eq_genus
    {D : Divisor (GlobalPlace k F)}
    (hD : riemannRochDefect (k := k) (F := F) D =
      functionFieldGenus (k := k) (F := F)) :
    globalAdeleTopSubmodule (k := k) (F := F) =
      globalAdeleFilter (k := k) (F := F) D +
        diagonalAdeleSubmodule (k := k) (F := F) := by sorry
