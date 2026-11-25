-- Prove2me | Theorems.Thm_PI_WAU_kset_open
-- name    : PI.WAU.kset_open
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:12:05.259033+00:00
-- url     : https://prove2.me/theorems/8a9c3898-4d12-49b6-a00a-23561f78df4f
-- title:
--   WAU: kset open
-- statement:
--   The WAU construction uses the kset open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ConstructionD.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ConstructionD.lean#L17-L19

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_KCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularIndex_PairwiseDisjointCosets
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open Formalism.MainNotions.S MeasureTheory Matrix Pointwise

theorem PI.WAU.kset_open (I : AutInst) : IsOpen I.Kset := by sorry
