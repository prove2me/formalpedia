-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coordinateUniformizerCoweight_rankThree_zero_one
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.coordinateUniformizerCoweight_rankThree_zero_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:36:58.462337+00:00
-- url     : https://prove2.me/theorems/549153a1-d43a-4819-9028-5c69b46b5b82
-- title:
--   Spherical Hecke: coordinate Uniformizer Coweight rank Three zero one
-- statement:
--   The Spherical Hecke construction uses the coordinate Uniformizer Coweight rank Three zero one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L161-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L161-L173

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.coordinateUniformizerCoweight_rankThree_zero_one
    (k : Type u) [Field k] :
    coordinateUniformizerCoweight k 3 0 *
        coordinateUniformizerCoweight k 3 1 =
      fundamentalCoweight k 3 2 := by sorry
