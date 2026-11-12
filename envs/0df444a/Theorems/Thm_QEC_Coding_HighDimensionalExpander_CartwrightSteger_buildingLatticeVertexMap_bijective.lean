-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_bijective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:45:32.77746+00:00
-- url     : https://prove2.me/theorems/8c31ee8f-d53e-4cc1-85da-c1286c31834b
-- title:
--   Cartwright Steger: building Lattice Vertex Map bijective
-- statement:
--   The Cartwright--Steger lattice acts simply transitively on the vertices
--   of the rank-three or rank-four affine building.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/SimpleTransitivity.lean#L260-L264
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/SimpleTransitivity.lean#L260-L264

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_bijective
    (P : BasePrime) (r : Rank) :
    Function.Bijective (buildingLatticeVertexMap P r) := by sorry
