-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZCohomology_oddEquiv_mk
-- name    : QEC.Coding.BDL26RZCohomology.oddEquiv_mk
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:47:55.877541+00:00
-- url     : https://prove2.me/theorems/47328404-c185-4435-88d6-ac78d810667e
-- title:
--   BDL26 RZCohomology: odd Equiv mk
-- statement:
--   Representative formula for every cocycle at every actual odd step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCohomology/Indexed.lean#L155-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCohomology/Indexed.lean#L155-L159

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Indexed
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps
open BDL26RZMap1CoordinateBridge
open scoped Classical
universe u

theorem QEC.Coding.BDL26RZCohomology.oddEquiv_mk (S : OddScale) (k : Nat)
    (v : Cocycle (state S (2 * k + 1)).presentation) :
    oddEquiv S k (classOf (state S (2 * k + 1)).presentation v) =
      classOf (state S (2 * k + 2)).presentation (oddCocycle S k v) := by sorry
