-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_stepEquiv_rz
-- name    : QEC.Coding.BDL26FiniteCohomology.stepEquiv_rz
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:28:29.176351+00:00
-- url     : https://prove2.me/theorems/f50266a5-6f17-4e2e-8d59-172068e3ac0f
-- title:
--   BDL26 Finite Cohomology: step Equiv rz
-- statement:
--   The BDL26 Finite Cohomology construction uses the step Equiv rz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L52-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L52-L57

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

theorem QEC.Coding.BDL26FiniteCohomology.stepEquiv_rz (S : OddScale) (n : Nat) (h : ¬ n % 2 = 0) :
    stepEquiv S n = BDL26RZCohomology.nextEquiv S n (state S n) h := by sorry
