-- Prove2me | Theorems.Thm_PI_LocHaarRRW_memO_of_integral
-- name    : PI.LocHaarRRW.memO_of_integral
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:35:07.825954+00:00
-- url     : https://prove2.me/theorems/2c6e491d-4ff6-4247-866a-a444565b6293
-- title:
--   Loc Haar RRW: mem O of integral
-- statement:
--   The Loc Haar RRW construction uses the mem O of integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/ExistsHaarOfSubgroup.lean#L101-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/ExistsHaarOfSubgroup.lean#L101-L102

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

theorem PI.LocHaarRRW.memO_of_integral {y : K} (h : IsIntegral 𝒪[K] y) : y ∈ 𝒪[K] := by sorry
