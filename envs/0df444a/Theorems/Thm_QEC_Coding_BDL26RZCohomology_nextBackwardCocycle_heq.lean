-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZCohomology_nextBackwardCocycle_heq
-- name    : QEC.Coding.BDL26RZCohomology.nextBackwardCocycle_heq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:47:05.369425+00:00
-- url     : https://prove2.me/theorems/041694ac-7fa4-439b-a268-3c7cda60a435
-- title:
--   BDL26 RZCohomology: next Backward Cocycle heq
-- statement:
--   The inverse remains the literal Q-parity map, up to the defining carrier
--   transport. This is map equality evidence, not an assumed H¹ isomorphism.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCohomology/Indexed.lean#L99-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCohomology/Indexed.lean#L99-L102

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

theorem QEC.Coding.BDL26RZCohomology.nextBackwardCocycle_heq (S : OddScale) (n : Nat) (C : ConstructionState)
    (h : ¬ n % 2 = 0) :
    HEq (nextBackwardCocycle S n C h) (backwardCocycle C.presentation C.admissible S) := by sorry
