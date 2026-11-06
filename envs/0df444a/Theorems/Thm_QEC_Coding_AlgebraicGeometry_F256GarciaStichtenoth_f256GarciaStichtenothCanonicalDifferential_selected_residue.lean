-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothCanonicalDifferential_selected_residue
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothCanonicalDifferential_selected_residue
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:40:12.247519+00:00
-- url     : https://prove2.me/theorems/f2840356-ebf0-4b37-8951-c80eb937aad0
-- title:
--   F256 Garcia Stichtenoth: f256 Garcia Stichtenoth Canonical Differential selected residue
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Garcia Stichtenoth Canonical Differential selected residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ExplicitGarciaStichtenothTower.lean#L234-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ExplicitGarciaStichtenothTower.lean#L234-L238

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothCanonicalDifferential_selected_residue (i : ℕ)
    (j : Fin (f256GarciaStichtenothLength i)) :
    Differential.simplePoleResidue (f256GarciaStichtenothSelectedPlace i j)
      (f256GarciaStichtenothCanonicalDifferentialAtPlace i (f256GarciaStichtenothSelectedPlace i j)) = 1 := by sorry
