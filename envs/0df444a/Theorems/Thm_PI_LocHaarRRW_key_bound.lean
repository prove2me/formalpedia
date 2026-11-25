-- Prove2me | Theorems.Thm_PI_LocHaarRRW_key_bound
-- name    : PI.LocHaarRRW.key_bound
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:35:23.230623+00:00
-- url     : https://prove2.me/theorems/53afd4fa-baa1-469d-b0fa-080e28a21539
-- title:
--   Loc Haar RRW: key bound
-- statement:
--   The Loc Haar RRW construction uses the key bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/IntegralMemNhdsAndSubsetCompactOfFinrankTwo.lean#L15-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/IntegralMemNhdsAndSubsetCompactOfFinrankTwo.lean#L15-L89

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

theorem PI.LocHaarRRW.key_bound [Nontrivial V] [Module.Finite K V] {θ : V} {d : K}
    (hθr : θ ∉ (algebraMap K V).range) (hθ : θ * θ = algebraMap K V d) (hdO : d ∈ 𝒪[K])
    {a b : K} (hx : IsIntegral 𝒪[K] (algebraMap K V a + algebraMap K V b * θ)) :
    2 * a ∈ 𝒪[K] ∧ 2 * b * d ∈ 𝒪[K] := by sorry
