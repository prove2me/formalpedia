-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_selectedLength_eq
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedLength_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:15:00.542448+00:00
-- url     : https://prove2.me/theorems/980dd5ef-90d1-4dfb-b40e-41a0fce9aed8
-- title:
--   F256 Garcia Stichtenoth: selected Length eq
-- statement:
--   The selected length is the literal `255 * 16^(i+2)` path count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Enumeration.lean#L70-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Enumeration.lean#L70-L72

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlaceDegree
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Equiv.Fintype
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Enumeration
set_option autoImplicit false
open Filter
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedLength_eq (i : ℕ) :
    selectedLength i = 255 * 16 ^ (i + 2) := by sorry
