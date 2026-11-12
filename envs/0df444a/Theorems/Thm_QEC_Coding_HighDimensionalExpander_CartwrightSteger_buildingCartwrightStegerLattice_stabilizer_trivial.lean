-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCartwrightStegerLattice_stabilizer_trivial
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCartwrightStegerLattice_stabilizer_trivial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:45:14.103258+00:00
-- url     : https://prove2.me/theorems/8d8991e7-d566-4676-9183-2171c076f566
-- title:
--   Cartwright Steger: building Cartwright Steger Lattice stabilizer trivial
-- statement:
--   The constructed Cartwright--Steger lattice has trivial stabilizer of
--   the standard building vertex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/SimpleTransitivity.lean#L223-L249
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/SimpleTransitivity.lean#L223-L249

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCartwrightStegerLattice_stabilizer_trivial
    (P : BasePrime) (r : Rank)
    (g : BuildingCartwrightStegerLattice P r)
    (hg : (g : Matrix.ProjGenLinGroup (Fin r.matrixRank)
        (BuildingLocalField P)) ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank) :
    g = 1 := by sorry
