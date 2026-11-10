-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCohomology_nextEquiv_mk
-- name    : QEC.Coding.BDL26RXCohomology.nextEquiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:17:53.704594+00:00
-- url     : https://prove2.me/theorems/526856e8-7006-45d7-bd4e-67b145b31e71
-- title:
--   BDL26 RXCohomology: next Equiv mk
-- statement:
--   The BDL26 RXCohomology construction uses the next Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Indexed.lean#L74-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Indexed.lean#L74-L89

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

theorem QEC.Coding.BDL26RXCohomology.nextEquiv_mk (S : OddScale) (n : Nat) (C : ConstructionState)
    (h : n % 2 = 0) (v : Cocycle C.presentation) :
    nextEquiv S n C h (classOf C.presentation v) =
      classOf (nextState S n C).presentation (nextCocycle S n C v) := by sorry
