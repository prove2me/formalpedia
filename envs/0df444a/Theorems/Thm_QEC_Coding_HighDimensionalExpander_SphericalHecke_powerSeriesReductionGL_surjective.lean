-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_powerSeriesReductionGL_surjective
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.powerSeriesReductionGL_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:26:16.873191+00:00
-- url     : https://prove2.me/theorems/9f76f6c9-75f4-427b-ab1d-80037bb890d3
-- title:
--   Spherical Hecke: power Series Reduction GL surjective
-- statement:
--   Reduction `GL_d(k[[X]]) → GL_d(k)` is onto, with the concrete
--   constant-matrix section above.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L38-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L38-L43

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.powerSeriesReductionGL_surjective
    (k : Type*) [Field k] (d : ℕ) :
    Function.Surjective (powerSeriesReductionGL k d) := by sorry
