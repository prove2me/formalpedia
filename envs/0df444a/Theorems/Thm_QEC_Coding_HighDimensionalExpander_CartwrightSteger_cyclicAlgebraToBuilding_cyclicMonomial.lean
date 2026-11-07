-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicMonomial
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_cyclicMonomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:04:57.975953+00:00
-- url     : https://prove2.me/theorems/7d552aa3-6bd6-4873-b41a-139e9436c989
-- title:
--   Cartwright Steger: cyclic Algebra To Building cyclic Monomial
-- statement:
--   The Cartwright Steger construction uses the cyclic Algebra To Building cyclic Monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingCyclicAlgebra.lean#L467-L473
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingCyclicAlgebra.lean#L467-L473

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebraBasis
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingSkewRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_cyclicMonomial
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r)
    (k : ℕ) (hk : k < r.matrixRank) :
    cyclicAlgebraToBuilding P r (cyclicMonomial P r c k) =
      buildingConstantMatrix P r c *
        buildingCyclicGeneratorMatrix P r ^ k := by sorry
