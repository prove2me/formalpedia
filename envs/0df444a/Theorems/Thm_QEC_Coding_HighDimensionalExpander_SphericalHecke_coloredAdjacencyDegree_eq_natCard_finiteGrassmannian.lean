-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coloredAdjacencyDegree_eq_natCard_finiteGrassmannian
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.coloredAdjacencyDegree_eq_natCard_finiteGrassmannian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:33:20.076788+00:00
-- url     : https://prove2.me/theorems/4b2d1e3d-811e-4421-b0a5-9dda8221bb84
-- title:
--   Spherical Hecke: colored Adjacency Degree eq nat Card finite Grassmannian
-- statement:
--   Consequently, the actual colored adjacency degree is the cardinality of
--   the finite Grassmannian.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L747-L757
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L747-L757

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.coloredAdjacencyDegree_eq_natCard_finiteGrassmannian
    (k : Type*) [Field k] [Finite k] (d r : ℕ) (hd : 0 < d) (hr : r ≤ d) :
    coloredAdjacencyDegree k d r =
      Nat.card
        (QEC.Coding.HighDimensionalExpander.FiniteGeometry.FiniteGrassmannian
          k (Fin d → k) r) := by sorry
