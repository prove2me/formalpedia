-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_injective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:45:10.676616+00:00
-- url     : https://prove2.me/theorems/5765a0f1-3e4d-4e45-9d3a-899fe21f8904
-- title:
--   Cartwright Steger: building Lattice Vertex Map injective
-- statement:
--   The lattice orbit map on building vertices is injective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/SimpleTransitivity.lean#L252-L256
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/SimpleTransitivity.lean#L252-L256

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (buildingLatticeVertexMap P r) := by sorry
