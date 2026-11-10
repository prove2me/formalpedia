-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZCohomology_nextEquiv_mk
-- name    : QEC.Coding.BDL26RZCohomology.nextEquiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:43:58.669203+00:00
-- url     : https://prove2.me/theorems/db4d729c-0b80-44c6-a10a-e32e81d633cc
-- title:
--   BDL26 RZCohomology: next Equiv mk
-- statement:
--   The BDL26 RZCohomology construction uses the next Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCohomology/Indexed.lean#L104-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCohomology/Indexed.lean#L104-L119

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

theorem QEC.Coding.BDL26RZCohomology.nextEquiv_mk (S : OddScale) (n : Nat) (C : ConstructionState)
    (h : ¬ n % 2 = 0) (v : Cocycle C.presentation) :
    nextEquiv S n C h (classOf C.presentation v) =
      classOf (nextState S n C).presentation (nextCocycle S n C v) := by sorry
