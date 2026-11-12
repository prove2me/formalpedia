-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLocalCyclicBasis_repr_integralMatrix
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLocalCyclicBasis_repr_integralMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:21:57.671609+00:00
-- url     : https://prove2.me/theorems/4a9536af-3d74-437c-89b6-095866427e22
-- title:
--   Cartwright Steger: building Local Cyclic Basis repr integral Matrix
-- statement:
--   Local cyclic coordinates of an included integral matrix are the images
--   of its integral cyclic coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingCyclicCoordinates.lean#L366-L427
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingCyclicCoordinates.lean#L366-L427

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticIntersection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_GlobalBuildingLattice
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLocalCyclicBasis_repr_integralMatrix
    (P : BasePrime) (r : Rank)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (BuildingIntegerRing P))
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (buildingLocalCyclicBasis P r).repr
        (M.map (SphericalHecke.integerEmbedding (BaseField P))) p =
      SphericalHecke.integerEmbedding (BaseField P)
        ((buildingIntegralCyclicBasis P r).repr M p) := by sorry
