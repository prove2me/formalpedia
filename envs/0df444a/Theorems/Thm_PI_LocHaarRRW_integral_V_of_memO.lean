-- Prove2me | Theorems.Thm_PI_LocHaarRRW_integral_V_of_memO
-- name    : PI.LocHaarRRW.integral_V_of_memO
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:29.398055+00:00
-- url     : https://prove2.me/theorems/7e1c9845-206f-4c34-8e2f-8f507f57ec9d
-- title:
--   Loc Haar RRW: integral V of mem O
-- statement:
--   The Loc Haar RRW construction uses the integral V of mem O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/ExistsHaarOfSubgroup.lean#L112-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/ExistsHaarOfSubgroup.lean#L112-L114

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
variable {K V : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CharZero K] [CommRing V] [Algebra K V]

theorem PI.LocHaarRRW.integral_V_of_memO [Nontrivial V] {y : K} (h : y ∈ 𝒪[K]) :
    IsIntegral 𝒪[K] (algebraMap K V y) := by sorry
