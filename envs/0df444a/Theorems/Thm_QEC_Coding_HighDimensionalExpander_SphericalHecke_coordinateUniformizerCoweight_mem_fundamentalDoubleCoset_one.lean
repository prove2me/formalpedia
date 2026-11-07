-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coordinateUniformizerCoweight_mem_fundamentalDoubleCoset_one
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.coordinateUniformizerCoweight_mem_fundamentalDoubleCoset_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:35:47.427814+00:00
-- url     : https://prove2.me/theorems/ad7a80bf-714f-4907-80a5-ed7e29c56d21
-- title:
--   Spherical Hecke: coordinate Uniformizer Coweight mem fundamental Double Coset one
-- statement:
--   Every one-coordinate uniformizer represents a color-one Cartan step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L91-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L91-L109

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.coordinateUniformizerCoweight_mem_fundamentalDoubleCoset_one
    (k : Type u) [Field k] [Finite k] {d : ℕ} (hd : 0 < d) (i : Fin d) :
    coordinateUniformizerCoweight k d i ∈
      fundamentalDoubleCoset k d 1 := by sorry
