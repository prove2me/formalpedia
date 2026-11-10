-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_prefixEquiv_mk
-- name    : QEC.Coding.BDL26FiniteCohomology.prefixEquiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:29:09.992136+00:00
-- url     : https://prove2.me/theorems/b65a540f-011c-49b4-8531-ee69e7903df5
-- title:
--   BDL26 Finite Cohomology: prefix Equiv mk
-- statement:
--   The composed quotient equivalence is induced by that very same prefix map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L112-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L112-L118

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

theorem QEC.Coding.BDL26FiniteCohomology.prefixEquiv_mk (S : OddScale) (n : Nat) (w : Cocycle S 0) :
    prefixEquiv S n (classOf S 0 w) = classOf S n (prefixCocycle S n w) := by sorry
