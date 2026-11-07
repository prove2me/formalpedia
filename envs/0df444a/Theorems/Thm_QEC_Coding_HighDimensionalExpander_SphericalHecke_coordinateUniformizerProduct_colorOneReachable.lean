-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coordinateUniformizerProduct_colorOneReachable
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.coordinateUniformizerProduct_colorOneReachable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:35:59.117587+00:00
-- url     : https://prove2.me/theorems/d22f83a9-4265-4614-8a37-797f1cefdd99
-- title:
--   Spherical Hecke: coordinate Uniformizer Product color One Reachable
-- statement:
--   A finite product of one-coordinate uniformizers is reachable from the
--   base vertex using color-one steps only.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L131-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L131-L159

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.coordinateUniformizerProduct_colorOneReachable
    (k : Type u) [Field k] [Finite k] {d : ℕ} (hd : 0 < d)
    (coordinates : List (Fin d)) :
    ColorOneReachable k d (QuotientGroup.mk 1)
      (QuotientGroup.mk
        ((coordinates.map (coordinateUniformizerCoweight k d)).prod)) := by sorry
