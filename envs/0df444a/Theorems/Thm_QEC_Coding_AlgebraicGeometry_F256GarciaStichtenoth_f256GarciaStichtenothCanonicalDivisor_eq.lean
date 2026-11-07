-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothCanonicalDivisor_eq
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothCanonicalDivisor_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:41:30.944731+00:00
-- url     : https://prove2.me/theorems/6e082457-c930-4d9b-91dc-8b75edcaab36
-- title:
--   F256 Garcia Stichtenoth: f256 Garcia Stichtenoth Canonical Divisor eq
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Garcia Stichtenoth Canonical Divisor eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ExplicitGarciaStichtenothTower.lean#L243-L247
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ExplicitGarciaStichtenothTower.lean#L243-L247

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothCanonicalDivisor_eq (i : ℕ) :
    f256GarciaStichtenothCanonicalDivisor i =
      (16 * (f256GarciaStichtenothAlpha i : ℤ) - 2) • f256GarciaStichtenothDivisorA i +
        ((f256GarciaStichtenothBeta i : ℤ) - 2) • f256GarciaStichtenothDivisorB i -
          f256GarciaStichtenothDivisorD i := by sorry
