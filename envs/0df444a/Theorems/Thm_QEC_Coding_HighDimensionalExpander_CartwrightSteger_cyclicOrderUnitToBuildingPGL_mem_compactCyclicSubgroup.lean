-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicOrderUnitToBuildingPGL_mem_compactCyclicSubgroup
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicOrderUnitToBuildingPGL_mem_compactCyclicSubgroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:26:47.011461+00:00
-- url     : https://prove2.me/theorems/44020340-c87f-443f-aa87-4c75fde8b297
-- title:
--   Cartwright Steger: cyclic Order Unit To Building PGL mem compact Cyclic Subgroup
-- statement:
--   A global order unit which is integral at the building place together
--   with its inverse has building projective image in the explicit compact cyclic
--   subgroup.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewCompatibility.lean#L152-L192
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewCompatibility.lean#L152-L192

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_OrderUnitReconstruction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingSkewRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCompatibility
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicOrderUnitToBuildingPGL_mem_compactCyclicSubgroup
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
    cyclicUnitToBuildingPGL P r
        (Units.map (cartwrightStegerOrderToCyclicAlgebra P r).toMonoidHom u) ∈
      BuildingCompactCyclicSubgroup P r := by sorry
