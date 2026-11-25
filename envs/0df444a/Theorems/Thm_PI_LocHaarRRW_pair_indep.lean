-- Prove2me | Theorems.Thm_PI_LocHaarRRW_pair_indep
-- name    : PI.LocHaarRRW.pair_indep
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:35:24.721859+00:00
-- url     : https://prove2.me/theorems/74f4a49c-ee2e-468e-90e6-1f66365ab8b3
-- title:
--   Loc Haar RRW: pair indep
-- statement:
--   The Loc Haar RRW construction uses the pair indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/ExistsHaarOfSubgroup.lean#L116-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/ExistsHaarOfSubgroup.lean#L116-L127

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

theorem PI.LocHaarRRW.pair_indep [Nontrivial V] {θ : V} (hθ : θ ∉ (algebraMap K V).range) (s t : K)
    (h : s • (1 : V) + t • θ = 0) : s = 0 ∧ t = 0 := by sorry
