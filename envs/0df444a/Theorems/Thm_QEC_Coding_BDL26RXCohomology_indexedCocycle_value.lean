-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCohomology_indexedCocycle_value
-- name    : QEC.Coding.BDL26RXCohomology.indexedCocycle_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:46:20.937731+00:00
-- url     : https://prove2.me/theorems/aac4677b-b895-40c1-b410-b43e70cf9fba
-- title:
--   BDL26 RXCohomology: indexed Cocycle value
-- statement:
--   Complete representative action is exactly the actual selected indexed map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Indexed.lean#L131-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Indexed.lean#L131-L136

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Indexed
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps
open BDL26RZMap1CoordinateBridge
open scoped Classical
universe u
open BDL26IndexedDecoder MultiscaleDecoder

theorem QEC.Coding.BDL26RXCohomology.indexedCocycle_value (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (v : ((indexedFamily S depth).complex i.castSucc).middleCocycleCode.carrier) :
    (indexedCocycle S depth i v).1 =
      ((indexedDecoderData S depth).selectedMap i).map1 v.1 := by sorry
