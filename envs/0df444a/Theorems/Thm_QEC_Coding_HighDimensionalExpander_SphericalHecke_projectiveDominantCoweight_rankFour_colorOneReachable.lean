-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominantCoweight_rankFour_colorOneReachable
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominantCoweight_rankFour_colorOneReachable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:37:15.961758+00:00
-- url     : https://prove2.me/theorems/8e41d634-f870-442e-823b-2c98e7f5d1b3
-- title:
--   Spherical Hecke: projective Dominant Coweight rank Four color One Reachable
-- statement:
--   Every normalized dominant rank-four Cartan vertex is reachable using
--   color-one steps.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L321-L369
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L321-L369

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominantCoweight_rankFour_colorOneReachable
    (k : Type u) [Field k] [Finite k]
    (weight : ProjectiveDominantCoweight 3) :
    ColorOneReachable k 4 (QuotientGroup.mk 1)
      (QuotientGroup.mk (dominantCoweight k weight.toDominant)) := by sorry
