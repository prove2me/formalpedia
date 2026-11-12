-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_indexedEquiv_prefix_mk
-- name    : QEC.Coding.BDL26FiniteCohomology.indexedEquiv_prefix_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:52:40.818783+00:00
-- url     : https://prove2.me/theorems/dadfe253-8c8d-40fd-8055-9e8892114c2b
-- title:
--   BDL26 Finite Cohomology: indexed Equiv prefix mk
-- statement:
--   The BDL26 Finite Cohomology construction uses the indexed Equiv prefix mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L227-L232
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L227-L232

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

theorem QEC.Coding.BDL26FiniteCohomology.indexedEquiv_prefix_mk (S : OddScale) (depth : Nat) (i : LevelIndex depth)
    (w : Cocycle S 0) :
    indexedEquiv S depth i
      (((indexedFamily S depth).complex i).middleCoboundaryInCocycles.mkQ
        (prefixCocycle S i.val w)) = BDL26SeedCohomology.coefficient w.1 := by sorry
