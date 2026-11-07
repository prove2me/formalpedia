-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_colorOneReachable_of_projectiveDominant
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.colorOneReachable_of_projectiveDominant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:33:22.475166+00:00
-- url     : https://prove2.me/theorems/105a57c1-d0dd-41c7-852b-8ae231fd430c
-- title:
--   Spherical Hecke: color One Reachable of projective Dominant
-- statement:
--   If all normalized dominant Cartan vertices are color-one reachable, then
--   the full building is color-one reachable.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L373-L415
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L373-L415

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.colorOneReachable_of_projectiveDominant
    (k : Type u) [Field k] [Finite k] (n : ℕ)
    (hdominant : ∀ weight : ProjectiveDominantCoweight n,
      ColorOneReachable k (n + 1) (QuotientGroup.mk 1)
        (QuotientGroup.mk (dominantCoweight k weight.toDominant)))
    (q : BuildingVertex k (n + 1)) :
    ColorOneReachable k (n + 1) (QuotientGroup.mk 1) q := by sorry
