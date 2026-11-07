-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_powerSeriesGeneralLinearToInteger_inverse
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.powerSeriesGeneralLinearToInteger_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:50:44.94835+00:00
-- url     : https://prove2.me/theorems/3acf06a8-c46b-486b-a69a-25ef7f681630
-- title:
--   Spherical Hecke: power Series General Linear To Integer inverse
-- statement:
--   The Spherical Hecke construction uses the power Series General Linear To Integer inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L52-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L52-L60

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.powerSeriesGeneralLinearToInteger_inverse
    (k : Type*) [Field k] (d : ℕ)
    (g : GL (Fin d) (Valued.integer (LocalFunctionField k))) :
    powerSeriesGeneralLinearToInteger k d
        (integerGeneralLinearToPowerSeries k d g) = g := by sorry
