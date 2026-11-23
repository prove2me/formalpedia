-- Prove2me | Theorems.Thm_PI_LocHaarRRW_inv_mem_integer
-- name    : PI.LocHaarRRW.inv_mem_integer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:37.498912+00:00
-- url     : https://prove2.me/theorems/ff2480fd-2942-48a2-81d9-e8ac2068d1f8
-- title:
--   Loc Haar RRW: inv mem integer
-- statement:
--   The Loc Haar RRW construction uses the inv mem integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/ExistsHaarOfSubgroup.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/ExistsHaarOfSubgroup.lean#L38-L42

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
variable {K}

theorem PI.LocHaarRRW.inv_mem_integer {x : K} (hx : x ∉ 𝒪[K]) : x⁻¹ ∈ 𝒪[K] := by sorry
