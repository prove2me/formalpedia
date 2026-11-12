-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCohomology_indexedEquiv_mk
-- name    : QEC.Coding.BDL26RXCohomology.indexedEquiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:46:49.178971+00:00
-- url     : https://prove2.me/theorems/f2231c3e-9faa-4edc-bcbe-2d119829b122
-- title:
--   BDL26 RXCohomology: indexed Equiv mk
-- statement:
--   The BDL26 RXCohomology construction uses the indexed Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Indexed.lean#L138-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Indexed.lean#L138-L144

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

theorem QEC.Coding.BDL26RXCohomology.indexedEquiv_mk (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0)
    (v : ((indexedFamily S depth).complex i.castSucc).middleCocycleCode.carrier) :
    indexedEquiv S depth i h
      (((indexedFamily S depth).complex i.castSucc).middleCoboundaryInCocycles.mkQ v) =
      ((indexedFamily S depth).complex i.succ).middleCoboundaryInCocycles.mkQ
        (indexedCocycle S depth i v) := by sorry
