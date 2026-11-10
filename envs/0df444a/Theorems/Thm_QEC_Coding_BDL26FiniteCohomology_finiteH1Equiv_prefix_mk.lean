-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_finiteH1Equiv_prefix_mk
-- name    : QEC.Coding.BDL26FiniteCohomology.finiteH1Equiv_prefix_mk
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:29:25.171854+00:00
-- url     : https://prove2.me/theorems/17301ce5-a6bb-4cb1-bc47-015d3fd85658
-- title:
--   BDL26 Finite Cohomology: finite H1 Equiv prefix mk
-- statement:
--   Every arbitrary seed representative has its original computed coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L142-L149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L142-L149

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

theorem QEC.Coding.BDL26FiniteCohomology.finiteH1Equiv_prefix_mk (S : OddScale) (n : Nat) (w : Cocycle S 0) :
    finiteH1Equiv S n (classOf S n (prefixCocycle S n w)) =
      BDL26SeedCohomology.coefficient w.1 := by sorry
