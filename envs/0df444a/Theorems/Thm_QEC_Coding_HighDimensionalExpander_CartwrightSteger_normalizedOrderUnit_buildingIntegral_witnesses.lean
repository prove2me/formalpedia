-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_normalizedOrderUnit_buildingIntegral_witnesses
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.normalizedOrderUnit_buildingIntegral_witnesses
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:43:50.976312+00:00
-- url     : https://prove2.me/theorems/db6429b9-392c-4eee-99db-5b13538b17de
-- title:
--   Cartwright Steger: normalized Order Unit building Integral witnesses
-- statement:
--   The normalized unit and its inverse have honest matrices over the
--   building integer ring, in the exact form required by coordinate
--   reconstruction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Stabilizer.lean#L196-L270
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Stabilizer.lean#L196-L270

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_RepresentationKernel
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.normalizedOrderUnit_buildingIntegral_witnesses
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerOrder P r)ˣ) (q : ℤ)
    (hcompact : orderUnitToBuildingPGL P r u ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank)
    (hq : SphericalHecke.localUnitOrder
        (Matrix.GeneralLinearGroup.det
          (cyclicUnitToBuildingGL P r (orderUnitToCyclicUnit P r u))) =
      (r.matrixRank : ℤ) * q) :
    (∃ M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingIntegerRing P),
      M.map (SphericalHecke.integerEmbedding (BaseField P)) =
        cyclicAlgebraToBuilding P r
          (cartwrightStegerOrderToCyclicAlgebra P r
            (normalizedOrderUnit P r u q : CartwrightStegerOrder P r))) ∧
    (∃ M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingIntegerRing P),
      M.map (SphericalHecke.integerEmbedding (BaseField P)) =
        cyclicAlgebraToBuilding P r
          (cartwrightStegerOrderToCyclicAlgebra P r
            (((normalizedOrderUnit P r u q)⁻¹ :
              (CartwrightStegerOrder P r)ˣ) :
                CartwrightStegerOrder P r))) := by sorry
