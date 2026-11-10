-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_step_left_inverse
-- name    : QEC.Coding.BDL26FiniteCohomology.step_left_inverse
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:48:51.976656+00:00
-- url     : https://prove2.me/theorems/58000fa8-85e9-4fc6-8cfa-0a06800d8d53
-- title:
--   BDL26 Finite Cohomology: step left inverse
-- statement:
--   The BDL26 Finite Cohomology construction uses the step left inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L67-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L67-L68

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

theorem QEC.Coding.BDL26FiniteCohomology.step_left_inverse (S : OddScale) (n : Nat) (v : H1 S n) :
    (stepEquiv S n).symm (stepEquiv S n v) = v := by sorry
