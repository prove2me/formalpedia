-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_indexed_left_inverse
-- name    : QEC.Coding.BDL26FiniteCohomology.indexed_left_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:29:57.968774+00:00
-- url     : https://prove2.me/theorems/cb14235e-903f-4e44-a63d-4acc146be45b
-- title:
--   BDL26 Finite Cohomology: indexed left inverse
-- statement:
--   The BDL26 Finite Cohomology construction uses the indexed left inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L234-L237
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L234-L237

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

theorem QEC.Coding.BDL26FiniteCohomology.indexed_left_inverse (S : OddScale) (depth : Nat) (i : LevelIndex depth)
    (v : ((indexedFamily S depth).complex i).middleCohomology) :
    (indexedEquiv S depth i).symm (indexedEquiv S depth i v) = v := by sorry
