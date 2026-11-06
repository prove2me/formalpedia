-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleQuotientRank_eq_sandwichRank
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleQuotientRank_eq_sandwichRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:13:49.581477+00:00
-- url     : https://prove2.me/theorems/9526ae06-1bd0-4552-bc2e-24e244530f06
-- title:
--   Global Place: global Adele Quotient Rank eq sandwich Rank
-- statement:
--   Once `A(E) + F` is the whole adele space, the quotient rank at `D` is
--   the corresponding finite sandwich rank.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleQuotient.lean#L81-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleQuotient.lean#L81-L118

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleQuotientRank_eq_sandwichRank
    {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E)
    (hfull : globalAdeleTopSubmodule (k := k) (F := F) =
      globalAdeleFilter (k := k) (F := F) E +
        diagonalAdeleSubmodule (k := k) (F := F)) :
    globalAdeleQuotientRank (k := k) (F := F) D =
      (globalAdeleSandwichRank (k := k) (F := F) D E hDE).toNat := by sorry
