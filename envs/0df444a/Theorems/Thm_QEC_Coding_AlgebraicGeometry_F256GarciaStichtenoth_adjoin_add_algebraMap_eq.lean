-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_adjoin_add_algebraMap_eq
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.adjoin_add_algebraMap_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:08:42.046122+00:00
-- url     : https://prove2.me/theorems/6f5902bb-d225-40e0-9a7a-6f9b79325289
-- title:
--   F256 Garcia Stichtenoth: adjoin add algebra Map eq
-- statement:
--   Translation by a base-field element does not change a simple extension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticCompositumCell.lean#L54-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticCompositumCell.lean#L54-L65

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalNormalization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_TrivialFieldExtension
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticCompositumCell
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.adjoin_add_algebraMap_eq {K L : Type*} [_root_.Field K] [_root_.Field L]
    [Algebra K L] (y : L) (c : K) :
    K⟮y + algebraMap K L c⟯ = K⟮y⟯ := by sorry
