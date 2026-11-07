-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_maximalCompact_eq_range_powerSeriesProjectiveMap
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.maximalCompact_eq_range_powerSeriesProjectiveMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:50:57.772444+00:00
-- url     : https://prove2.me/theorems/d17edfc4-9505-400b-975d-6b44cc234ab2
-- title:
--   Spherical Hecke: maximal Compact eq range power Series Projective Map
-- statement:
--   The analytically defined maximal compact subgroup is exactly the
--   projective image of `GL_d(k[[X]])`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L77-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L77-L89

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.maximalCompact_eq_range_powerSeriesProjectiveMap
    (k : Type*) [Field k] (d : ℕ) :
    (maximalCompact k d :
      Set (PGL(Fin d, LocalFunctionField k))) =
      Set.range (powerSeriesProjectiveMap k d) := by sorry
