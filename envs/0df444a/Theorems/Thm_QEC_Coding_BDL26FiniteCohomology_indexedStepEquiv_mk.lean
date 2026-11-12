-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_indexedStepEquiv_mk
-- name    : QEC.Coding.BDL26FiniteCohomology.indexedStepEquiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:50:38.254296+00:00
-- url     : https://prove2.me/theorems/501e1eea-d7ae-4ed1-9793-3f1d6b29da63
-- title:
--   BDL26 Finite Cohomology: indexed Step Equiv mk
-- statement:
--   The BDL26 Finite Cohomology construction uses the indexed Step Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L220-L225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L220-L225

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

theorem QEC.Coding.BDL26FiniteCohomology.indexedStepEquiv_mk (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (w : ((indexedFamily S depth).complex i.castSucc).middleCocycleCode.carrier) :
    indexedStepEquiv S depth i
      (((indexedFamily S depth).complex i.castSucc).middleCoboundaryInCocycles.mkQ w) =
      ((indexedFamily S depth).complex i.succ).middleCoboundaryInCocycles.mkQ
        (indexedStepCocycle S depth i w) := by sorry
