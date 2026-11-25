-- Prove2me | Theorems.Thm_PI_LocHaarRRW_sigmaCompactSpace_lf
-- name    : PI.LocHaarRRW.sigmaCompactSpace_lf
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:35:13.295245+00:00
-- url     : https://prove2.me/theorems/7c9b39d3-9dc9-4c27-a888-bc3b7b18ae8b
-- title:
--   Loc Haar RRW: sigma Compact Space lf
-- statement:
--   The Loc Haar RRW construction uses the sigma Compact Space lf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/ExistsHaarOfSubgroup.lean#L44-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/ExistsHaarOfSubgroup.lean#L44-L77

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalHaarSubgroup_ExistsHaarOfSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel MeasureTheory Topology Polynomial
open PI PI.LocHaarRRW
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem PI.LocHaarRRW.sigmaCompactSpace_lf : SigmaCompactSpace K := by sorry
