-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothDivisorB_support_disjoint_D
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothDivisorB_support_disjoint_D
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:51:12.144206+00:00
-- url     : https://prove2.me/theorems/c0c1070f-6bf2-4252-b9f4-d3263981ec48
-- title:
--   F256 Garcia Stichtenoth: f256 Garcia Stichtenoth Divisor B support disjoint D
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Garcia Stichtenoth Divisor B support disjoint D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ExplicitGarciaStichtenothTower.lean#L163-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ExplicitGarciaStichtenothTower.lean#L163-L165

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureGenus
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedFibreSeparation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWZeroRamification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWRamification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter FunctionFieldDifferential
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothDivisorB_support_disjoint_D (i : ℕ) :
    Disjoint (f256GarciaStichtenothDivisorB i).support (f256GarciaStichtenothDivisorD i).support := by sorry
