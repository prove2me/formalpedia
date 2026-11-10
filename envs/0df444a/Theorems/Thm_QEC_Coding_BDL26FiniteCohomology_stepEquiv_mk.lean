-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_stepEquiv_mk
-- name    : QEC.Coding.BDL26FiniteCohomology.stepEquiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:27:15.040235+00:00
-- url     : https://prove2.me/theorems/61fcc974-4fc5-4d89-b479-105a5b93e71a
-- title:
--   BDL26 Finite Cohomology: step Equiv mk
-- statement:
--   The BDL26 Finite Cohomology construction uses the step Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L59-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L59-L65

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26FiniteCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26FiniteCohomology.stepEquiv_mk (S : OddScale) (n : Nat) (w : Cocycle S n) :
    stepEquiv S n (classOf S n w) = classOf S (n+1) (stepCocycle S n w) := by sorry
