-- Prove2me | Theorems.Thm_PI_LocHaarRRW_exists_sq
-- name    : PI.LocHaarRRW.exists_sq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:34:41.079668+00:00
-- url     : https://prove2.me/theorems/a21b25e9-c743-48f4-b83f-a9b6517f3d11
-- title:
--   Loc Haar RRW: exists sq
-- statement:
--   The Loc Haar RRW construction uses the exists sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/ExistsHaarOfSubgroup.lean#L129-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/ExistsHaarOfSubgroup.lean#L129-L185

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

theorem PI.LocHaarRRW.exists_sq [Module.Free K V] (hr : Module.finrank K V = 2) [IsReduced V] :
    ∃ θ : V, ∃ d : K, θ ∉ (algebraMap K V).range ∧ θ * θ = algebraMap K V d ∧ d ≠ 0 ∧
      d ∈ 𝒪[K] := by sorry
