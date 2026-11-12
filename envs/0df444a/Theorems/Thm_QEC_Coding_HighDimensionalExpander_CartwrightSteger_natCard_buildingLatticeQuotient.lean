-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_natCard_buildingLatticeQuotient
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_buildingLatticeQuotient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:28:25.537166+00:00
-- url     : https://prove2.me/theorems/90dcf2a0-ef7a-4e62-a012-ae10f35ce00b
-- title:
--   Cartwright Steger: nat Card building Lattice Quotient
-- statement:
--   The Cartwright Steger construction uses the nat Card building Lattice Quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingQuotient.lean#L319-L325
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingQuotient.lean#L319-L325

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_Relations
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_buildingLatticeQuotient
    (P : BasePrime) (r : Rank) (level : Nat) :
    Nat.card
        (BuildingCartwrightStegerLattice P r ⧸
          BuildingCartwrightStegerCongruenceSubgroup P r level) =
      Nat.card (IndexCartwrightStegerImage P r level) := by sorry
