-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coordinateUniformizerCoweight_rankFour_zero_one_two
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.coordinateUniformizerCoweight_rankFour_zero_one_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:37:06.145145+00:00
-- url     : https://prove2.me/theorems/a8f9fcc9-e305-4a6a-b2b3-921b5ec76eb8
-- title:
--   Spherical Hecke: coordinate Uniformizer Coweight rank Four zero one two
-- statement:
--   The Spherical Hecke construction uses the coordinate Uniformizer Coweight rank Four zero one two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L189-L202
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L189-L202

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.coordinateUniformizerCoweight_rankFour_zero_one_two
    (k : Type u) [Field k] :
    coordinateUniformizerCoweight k 4 0 *
          coordinateUniformizerCoweight k 4 1 *
        coordinateUniformizerCoweight k 4 2 =
      fundamentalCoweight k 4 3 := by sorry
