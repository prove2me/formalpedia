-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothCanonicalDifferentialAtPlace_coe
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothCanonicalDifferentialAtPlace_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:41:30.879807+00:00
-- url     : https://prove2.me/theorems/fdcc72a5-ec79-42cf-a98a-57612513de1a
-- title:
--   F256 Garcia Stichtenoth: f256 Garcia Stichtenoth Canonical Differential At Place coe
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Garcia Stichtenoth Canonical Differential At Place coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ExplicitGarciaStichtenothTower.lean#L229-L232
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ExplicitGarciaStichtenothTower.lean#L229-L232

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothCanonicalDifferentialAtPlace_coe (i : ℕ)
    (P : GlobalPlace F256 (f256GarciaStichtenothField i)) :
    (f256GarciaStichtenothCanonicalDifferentialAtPlace i P : Differential F256 (f256GarciaStichtenothField i)) =
      f256GarciaStichtenothCanonicalDifferential i := by sorry
