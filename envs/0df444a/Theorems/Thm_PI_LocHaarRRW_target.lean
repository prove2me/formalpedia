-- Prove2me | Theorems.Thm_PI_LocHaarRRW_target
-- name    : PI.LocHaarRRW.target
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:35:42.004401+00:00
-- url     : https://prove2.me/theorems/b60c1975-3ecf-45f7-a7a9-b16f1328057a
-- title:
--   Loc Haar RRW: target
-- statement:
--   The Loc Haar RRW construction uses the target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/MemOrdR.lean#L36-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/MemOrdR.lean#L36-L78

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocHaarRR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalHaarSubgroup_IntegralMemNhdsAndSubsetCompactOfFinrankTwo
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalHaarSubgroup_MemOrdR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel MeasureTheory Topology IsDedekindDomain NumberField
open PI PI.LocHaarRRW

theorem PI.LocHaarRRW.target : PI.LocHaarRR.Target := by sorry
