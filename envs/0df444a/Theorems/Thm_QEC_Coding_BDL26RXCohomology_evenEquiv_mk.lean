-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCohomology_evenEquiv_mk
-- name    : QEC.Coding.BDL26RXCohomology.evenEquiv_mk
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:46:29.742852+00:00
-- url     : https://prove2.me/theorems/4f651752-abe3-4815-ae4b-8a8303922b96
-- title:
--   BDL26 RXCohomology: even Equiv mk
-- statement:
--   Representative formula for every cocycle at every actual even step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Indexed.lean#L110-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Indexed.lean#L110-L114

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

theorem QEC.Coding.BDL26RXCohomology.evenEquiv_mk (S : OddScale) (k : Nat)
    (v : Cocycle (state S (2 * k)).presentation) :
    evenEquiv S k (classOf (state S (2 * k)).presentation v) =
      classOf (state S (2 * k + 1)).presentation (evenCocycle S k v) := by sorry
