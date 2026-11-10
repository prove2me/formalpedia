-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZCohomology_nextEquiv_symm_mk
-- name    : QEC.Coding.BDL26RZCohomology.nextEquiv_symm_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:44:40.867708+00:00
-- url     : https://prove2.me/theorems/34c3fcc1-c02b-4ff4-8d64-1a06925146e7
-- title:
--   BDL26 RZCohomology: next Equiv symm mk
-- statement:
--   The BDL26 RZCohomology construction uses the next Equiv symm mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCohomology/Indexed.lean#L121-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCohomology/Indexed.lean#L121-L129

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Indexed
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps
open BDL26RZMap1CoordinateBridge
open scoped Classical
universe u

theorem QEC.Coding.BDL26RZCohomology.nextEquiv_symm_mk (S : OddScale) (n : Nat) (C : ConstructionState)
    (h : ¬ n % 2 = 0) (w : Cocycle (nextState S n C).presentation) :
    (nextEquiv S n C h).symm (classOf (nextState S n C).presentation w) =
      classOf C.presentation (nextBackwardCocycle S n C h w) := by sorry
