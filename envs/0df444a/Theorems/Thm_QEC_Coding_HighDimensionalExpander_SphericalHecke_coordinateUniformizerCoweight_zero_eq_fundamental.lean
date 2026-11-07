-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coordinateUniformizerCoweight_zero_eq_fundamental
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.coordinateUniformizerCoweight_zero_eq_fundamental
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:33:11.485957+00:00
-- url     : https://prove2.me/theorems/d36ac833-7059-41d3-a43e-18a34d1a961d
-- title:
--   Spherical Hecke: coordinate Uniformizer Coweight zero eq fundamental
-- statement:
--   The zeroth coordinate uniformizer is the distinguished color-one Cartan
--   representative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L75-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L75-L88

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.coordinateUniformizerCoweight_zero_eq_fundamental
    (k : Type u) [Field k] {d : ℕ} (hd : 0 < d) :
    coordinateUniformizerCoweight k d ⟨0, hd⟩ =
      fundamentalCoweight k d 1 := by sorry
