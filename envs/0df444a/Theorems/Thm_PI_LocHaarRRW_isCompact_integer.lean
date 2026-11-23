-- Prove2me | Theorems.Thm_PI_LocHaarRRW_isCompact_integer
-- name    : PI.LocHaarRRW.isCompact_integer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:58:45.808999+00:00
-- url     : https://prove2.me/theorems/eec41d03-eb4a-4973-a400-3f7ecb02bfa1
-- title:
--   Loc Haar RRW: is Compact integer
-- statement:
--   The Loc Haar RRW construction uses the is Compact integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/ExistsHaarOfSubgroup.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/ExistsHaarOfSubgroup.lean#L32-L33

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

theorem PI.LocHaarRRW.isCompact_integer : IsCompact (𝒪[K] : Set K) := by sorry
