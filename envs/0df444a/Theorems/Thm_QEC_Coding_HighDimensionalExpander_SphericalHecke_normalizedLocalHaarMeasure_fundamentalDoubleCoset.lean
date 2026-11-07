-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_normalizedLocalHaarMeasure_fundamentalDoubleCoset
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.normalizedLocalHaarMeasure_fundamentalDoubleCoset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:33:09.620967+00:00
-- url     : https://prove2.me/theorems/19b9960e-d794-43c3-9069-9b6219a48fe3
-- title:
--   Spherical Hecke: normalized Local Haar Measure fundamental Double Coset
-- statement:
--   Exact analytic normalization: the Haar volume of a fundamental double
--   coset is the cardinality of its finite right-`K` quotient, hence the actual
--   colored adjacency degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L599-L617
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L599-L617

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.normalizedLocalHaarMeasure_fundamentalDoubleCoset
    (k : Type u) [Field k] [Finite k] (d r : ℕ) :
    normalizedLocalHaarMeasure k d (fundamentalDoubleCoset k d r) =
      coloredAdjacencyDegree k d r := by sorry
