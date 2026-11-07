-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalHeckeFunction_ne_zero_iff_adjacent
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalHeckeFunction_ne_zero_iff_adjacent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:33:47.597197+00:00
-- url     : https://prove2.me/theorems/8701f409-2509-4bc7-b0f9-ecad4f33e136
-- title:
--   Spherical Hecke: fundamental Hecke Function ne zero iff adjacent
-- statement:
--   The fundamental Hecke function is exactly the indicator of the colored
--   building adjacency relation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L435-L444
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L435-L444

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalHeckeFunction_ne_zero_iff_adjacent
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (gx gy : HeckeGroup k d) :
    fundamentalHeckeFunction k d r (gx⁻¹ * gy) ≠ 0 ↔
      ColoredBuildingAdjacent k d r
        (QuotientGroup.mk gx) (QuotientGroup.mk gy) := by sorry
