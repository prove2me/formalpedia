-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integralProjectiveMap_eq_powerSeriesProjectiveMap_inverse
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.integralProjectiveMap_eq_powerSeriesProjectiveMap_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:50:53.871079+00:00
-- url     : https://prove2.me/theorems/55398c94-9443-47f7-a3ef-a12eff11ee82
-- title:
--   Spherical Hecke: integral Projective Map eq power Series Projective Map inverse
-- statement:
--   The Spherical Hecke construction uses the integral Projective Map eq power Series Projective Map inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L62-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L62-L73

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.integralProjectiveMap_eq_powerSeriesProjectiveMap_inverse
    (k : Type*) [Field k] (d : ℕ)
    (g : GL (Fin d) (Valued.integer (LocalFunctionField k))) :
    integralProjectiveMap k d g =
      powerSeriesProjectiveMap k d
        (integerGeneralLinearToPowerSeries k d g) := by sorry
