-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_powerSeriesReductionGL_constantGeneralLinearLift
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.powerSeriesReductionGL_constantGeneralLinearLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:44:00.633222+00:00
-- url     : https://prove2.me/theorems/7103e879-df91-4240-aebb-5ebe63cbf198
-- title:
--   Spherical Hecke: power Series Reduction GL constant General Linear Lift
-- statement:
--   The Spherical Hecke construction uses the power Series Reduction GL constant General Linear Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L28-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L28-L34

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.powerSeriesReductionGL_constantGeneralLinearLift
    (k : Type*) [Field k] (d : ℕ)
    (g : GL (Fin d) k) :
    powerSeriesReductionGL k d (constantGeneralLinearLift k d g) = g := by sorry
