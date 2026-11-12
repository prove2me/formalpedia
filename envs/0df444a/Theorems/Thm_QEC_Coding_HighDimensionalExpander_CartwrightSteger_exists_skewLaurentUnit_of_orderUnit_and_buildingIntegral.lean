-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_skewLaurentUnit_of_orderUnit_and_buildingIntegral
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_skewLaurentUnit_of_orderUnit_and_buildingIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:24:32.969222+00:00
-- url     : https://prove2.me/theorems/a8109519-cdb2-4347-8ed4-ec8e1e61f8f1
-- title:
--   Cartwright Steger: exists skew Laurent Unit of order Unit and building Integral
-- statement:
--   An order unit whose two unit components are building-integral has a
--   genuine preimage in the unit group of the integral skew Laurent ring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/OrderUnitReconstruction.lean#L16-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/OrderUnitReconstruction.lean#L16-L56

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewFaithfulness
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstructionTheorem
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_OrderUnitReconstruction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_skewLaurentUnit_of_orderUnit_and_buildingIntegral
    (P : BasePrime) (r : Rank) (u : (CartwrightStegerOrder P r)ˣ)
    (hlocal : ∃ M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingIntegerRing P),
      M.map (SphericalHecke.integerEmbedding (BaseField P)) =
        cyclicAlgebraToBuilding P r
          (cartwrightStegerOrderToCyclicAlgebra P r
            (u : CartwrightStegerOrder P r)))
    (hlocalInv : ∃ M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingIntegerRing P),
      M.map (SphericalHecke.integerEmbedding (BaseField P)) =
        cyclicAlgebraToBuilding P r
          (cartwrightStegerOrderToCyclicAlgebra P r
            ((u⁻¹ : (CartwrightStegerOrder P r)ˣ) :
              CartwrightStegerOrder P r))) :
    ∃ v : (CartwrightStegerSkewLaurentRing P r)ˣ,
      skewLaurentToGlobalMatrix P r v =
        (cartwrightStegerOrderToCyclicAlgebra P r
          (u : CartwrightStegerOrder P r)).1 := by sorry
