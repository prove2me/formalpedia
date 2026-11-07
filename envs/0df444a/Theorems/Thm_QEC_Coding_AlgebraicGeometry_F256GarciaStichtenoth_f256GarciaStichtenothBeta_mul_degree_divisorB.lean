-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothBeta_mul_degree_divisorB
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothBeta_mul_degree_divisorB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:39:17.570731+00:00
-- url     : https://prove2.me/theorems/50e35ffc-5665-4c75-a37f-8363dd881dfb
-- title:
--   F256 Garcia Stichtenoth: f256 Garcia Stichtenoth Beta mul degree divisor B
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Garcia Stichtenoth Beta mul degree divisor B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ExplicitGarciaStichtenothTower.lean#L189-L193
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ExplicitGarciaStichtenothTower.lean#L189-L193

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothBeta_mul_degree_divisorB (i : ℕ) :
    (f256GarciaStichtenothBeta i : ℤ) *
      Divisor.degree GlobalPlace.residueDegree (f256GarciaStichtenothDivisorB i) =
        (f256GarciaStichtenothLength i / 15 : ℕ) := by sorry
