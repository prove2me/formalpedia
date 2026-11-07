-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFour_colorOneReachable
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFour_colorOneReachable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:37:20.042196+00:00
-- url     : https://prove2.me/theorems/47c5f5ad-89e8-4dd6-9192-8ee887bb213a
-- title:
--   Spherical Hecke: rank Four color One Reachable
-- statement:
--   The rank-four affine building is connected by directed color-one
--   steps.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L427-L431
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L427-L431

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFour_colorOneReachable
    (k : Type u) [Field k] [Finite k] (q : BuildingVertex k 4) :
    ColorOneReachable k 4 (QuotientGroup.mk 1) q := by sorry
