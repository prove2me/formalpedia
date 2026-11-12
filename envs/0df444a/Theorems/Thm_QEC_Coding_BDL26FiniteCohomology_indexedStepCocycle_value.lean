-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_indexedStepCocycle_value
-- name    : QEC.Coding.BDL26FiniteCohomology.indexedStepCocycle_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:50:08.6057+00:00
-- url     : https://prove2.me/theorems/2e3ea1e7-e1d5-460f-bc13-7686c2d0d0c1
-- title:
--   BDL26 Finite Cohomology: indexed Step Cocycle value
-- statement:
--   The BDL26 Finite Cohomology construction uses the indexed Step Cocycle value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L213-L218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L213-L218

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26FiniteCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26FiniteCohomology.indexedStepCocycle_value (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (w : ((indexedFamily S depth).complex i.castSucc).middleCocycleCode.carrier) :
    (indexedStepCocycle S depth i w).1 =
      ((indexedDecoderData S depth).selectedMap i).map1 w.1 := by sorry
