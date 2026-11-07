-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeHecke_ne_zero_iff_adjacent
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeHecke_ne_zero_iff_adjacent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:41:48.843349+00:00
-- url     : https://prove2.me/theorems/02ac7c94-937c-444a-be6a-18b1cfd9faa0
-- title:
--   Spherical Hecke: rank Three Hecke ne zero iff adjacent
-- statement:
--   The Spherical Hecke construction uses the rank Three Hecke ne zero iff adjacent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L849-L854
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L849-L854

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeHecke_ne_zero_iff_adjacent
    (k : Type u) [Field k] [Finite k] (color : RankThreeColor)
    (gx gy : HeckeGroup k 3) :
    fundamentalHeckeFunction k 3 (color.val + 1) (gx⁻¹ * gy) ≠ 0 ↔
      RankThreeAdjacent k color (QuotientGroup.mk gx) (QuotientGroup.mk gy) := by sorry
