-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_colorOneReachable_smul
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.colorOneReachable_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:33:15.773736+00:00
-- url     : https://prove2.me/theorems/9c3147a8-81da-4d66-8594-2fde72e7127c
-- title:
--   Spherical Hecke: color One Reachable smul
-- statement:
--   Left translation preserves color-one reachability.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L118-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L118-L127

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise
open HeckeFunction
universe u

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.colorOneReachable_smul
    (k : Type u) [Field k] [Finite k] (d : ℕ)
    (g : HeckeGroup k d) {x y : BuildingVertex k d}
    (hxy : ColorOneReachable k d x y) :
    ColorOneReachable k d (g • x) (g • y) := by sorry
