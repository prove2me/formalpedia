-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZCohomology_oddCocycle_value
-- name    : QEC.Coding.BDL26RZCohomology.oddCocycle_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:46:54.155253+00:00
-- url     : https://prove2.me/theorems/6228e5f2-c8af-44d7-9f48-aa9ce689b377
-- title:
--   BDL26 RZCohomology: odd Cocycle value
-- statement:
--   The actual forward cocycle word is literally the existing selected map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCohomology/Indexed.lean#L150-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCohomology/Indexed.lean#L150-L152

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

theorem QEC.Coding.BDL26RZCohomology.oddCocycle_value (S : OddScale) (k : Nat)
    (v : Cocycle (state S (2 * k + 1)).presentation) :
    (oddCocycle S k v).1 = stepMap1 S (2 * k + 1) v.1 := by sorry
