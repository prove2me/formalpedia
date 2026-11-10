-- Prove2me | Theorems.Thm_QEC_Coding_BDL26SeedCohomology_stateZeroEquivalence_classOf
-- name    : QEC.Coding.BDL26SeedCohomology.stateZeroEquivalence_classOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:33:24.929378+00:00
-- url     : https://prove2.me/theorems/801933b9-729b-4404-b5e6-b3e15632963b
-- title:
--   BDL26 Seed Cohomology: state Zero Equivalence class Of
-- statement:
--   The BDL26 Seed Cohomology construction uses the state Zero Equivalence class Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/SeedCohomology.lean#L187-L188
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/SeedCohomology.lean#L187-L188

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26SeedCohomology
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26RZMap1CoordinateBridge BDL26LevelTwoDistance

theorem QEC.Coding.BDL26SeedCohomology.stateZeroEquivalence_classOf (S : OddScale) (w : Cocycle) :
    stateZeroEquivalence S (classOf w) = coefficient w.1 := by sorry

attribute [defeq] QEC.Coding.BDL26SeedCohomology.stateZeroEquivalence_classOf
