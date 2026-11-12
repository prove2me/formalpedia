-- Prove2me | Theorems.Thm_QEC_Coding_BDL26SeedCohomology_seed_class_nonzero
-- name    : QEC.Coding.BDL26SeedCohomology.seed_class_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:58:24.406611+00:00
-- url     : https://prove2.me/theorems/f077a4c2-2111-4855-893a-8707fbbe0e4f
-- title:
--   BDL26 Seed Cohomology: seed class nonzero
-- statement:
--   The BDL26 Seed Cohomology construction uses the seed class nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/SeedCohomology.lean#L169-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/SeedCohomology.lean#L169-L174

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26SeedCohomology
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26RZMap1CoordinateBridge BDL26LevelTwoDistance

theorem QEC.Coding.BDL26SeedCohomology.seed_class_nonzero : classOf seedElement ≠ 0 := by sorry
