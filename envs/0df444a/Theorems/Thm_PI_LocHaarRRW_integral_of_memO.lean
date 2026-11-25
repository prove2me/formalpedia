-- Prove2me | Theorems.Thm_PI_LocHaarRRW_integral_of_memO
-- name    : PI.LocHaarRRW.integral_of_memO
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:34:47.657166+00:00
-- url     : https://prove2.me/theorems/e85b1f9e-cbd8-4eca-a891-a5aebd21f668
-- title:
--   Loc Haar RRW: integral of mem O
-- statement:
--   The Loc Haar RRW construction uses the integral of mem O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/ExistsHaarOfSubgroup.lean#L104-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/ExistsHaarOfSubgroup.lean#L104-L106

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

theorem PI.LocHaarRRW.integral_of_memO {y : K} (h : y ∈ 𝒪[K]) : IsIntegral 𝒪[K] y := by sorry
