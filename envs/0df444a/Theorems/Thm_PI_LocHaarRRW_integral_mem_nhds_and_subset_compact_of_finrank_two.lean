-- Prove2me | Theorems.Thm_PI_LocHaarRRW_integral_mem_nhds_and_subset_compact_of_finrank_two
-- name    : PI.LocHaarRRW.integral_mem_nhds_and_subset_compact_of_finrank_two
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:34:49.952082+00:00
-- url     : https://prove2.me/theorems/9dbea33a-4445-4022-bda2-a0ab2aafaa0a
-- title:
--   Loc Haar RRW: integral mem nhds and subset compact of finrank two
-- statement:
--   The Loc Haar RRW construction uses the integral mem nhds and subset compact of finrank two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/IntegralMemNhdsAndSubsetCompactOfFinrankTwo.lean#L91-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/IntegralMemNhdsAndSubsetCompactOfFinrankTwo.lean#L91-L162

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalHaarSubgroup_ExistsHaarOfSubgroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalHaarSubgroup_IntegralMemNhdsAndSubsetCompactOfFinrankTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Topology Polynomial
open PI PI.LocHaarRRW
variable {K V : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CharZero K] [CommRing V] [Algebra K V]

theorem PI.LocHaarRRW.integral_mem_nhds_and_subset_compact_of_finrank_two [Module.Free K V] (hr : Module.finrank K V = 2) [IsReduced V]
    [TopologicalSpace V] [IsModuleTopology K V]
    (O : Subring V) (hO : ∀ x, x ∈ O ↔ IsIntegral 𝒪[K] x) :
    ∃ _ : K × K ≃ₜ V, (O : Set V) ∈ 𝓝 (0 : V) ∧ ∃ C : Set V, IsCompact C ∧ (O : Set V) ⊆ C := by sorry
