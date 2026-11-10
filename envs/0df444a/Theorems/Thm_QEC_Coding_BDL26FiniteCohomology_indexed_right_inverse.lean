-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_indexed_right_inverse
-- name    : QEC.Coding.BDL26FiniteCohomology.indexed_right_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:36:14.221187+00:00
-- url     : https://prove2.me/theorems/7390a81a-d800-4f4f-bff4-45460cb5edf7
-- title:
--   BDL26 Finite Cohomology: indexed right inverse
-- statement:
--   The BDL26 Finite Cohomology construction uses the indexed right inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L239-L241
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L239-L241

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26FiniteCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26FiniteCohomology.indexed_right_inverse (S : OddScale) (depth : Nat) (i : LevelIndex depth) (c : Field) :
    indexedEquiv S depth i ((indexedEquiv S depth i).symm c) = c := by sorry
