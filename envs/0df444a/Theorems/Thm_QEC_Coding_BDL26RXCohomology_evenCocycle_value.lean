-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCohomology_evenCocycle_value
-- name    : QEC.Coding.BDL26RXCohomology.evenCocycle_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:46:13.742698+00:00
-- url     : https://prove2.me/theorems/e1b84102-7eb5-4b00-aa68-a19324299aed
-- title:
--   BDL26 RXCohomology: even Cocycle value
-- statement:
--   The actual forward cocycle word is literally the existing selected map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Indexed.lean#L105-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Indexed.lean#L105-L107

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

theorem QEC.Coding.BDL26RXCohomology.evenCocycle_value (S : OddScale) (k : Nat)
    (v : Cocycle (state S (2 * k)).presentation) :
    (evenCocycle S k v).1 = stepMap1 S (2 * k) v.1 := by sorry
