-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalCoweight_rankFour_colorOneReachable
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalCoweight_rankFour_colorOneReachable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:37:17.308213+00:00
-- url     : https://prove2.me/theorems/b517a4a2-4bd9-4ebc-a07d-9f415227141e
-- title:
--   Spherical Hecke: fundamental Coweight rank Four color One Reachable
-- statement:
--   Every fundamental rank-four Cartan vertex is reachable using only
--   color-one steps.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L233-L265
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L233-L265

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalCoweight_rankFour_colorOneReachable
    (k : Type u) [Field k] [Finite k] (color : Fin 3) :
    ColorOneReachable k 4 (QuotientGroup.mk 1)
      (QuotientGroup.mk
        (fundamentalCoweight k 4 (color.val + 1))) := by sorry
