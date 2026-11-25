-- Prove2me | Theorems.Thm_PI_LocHaarRRW_exists_haar_of_subgroup
-- name    : PI.LocHaarRRW.exists_haar_of_subgroup
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:34:50.389581+00:00
-- url     : https://prove2.me/theorems/ba1de5d4-bc9e-4040-bf6c-a279be4e13cf
-- title:
--   Loc Haar RRW: exists haar of subgroup
-- statement:
--   The Loc Haar RRW construction uses the exists haar of subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/ExistsHaarOfSubgroup.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/ExistsHaarOfSubgroup.lean#L14-L24

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
variable {V : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V]

theorem PI.LocHaarRRW.exists_haar_of_subgroup [SigmaCompactSpace V] (R : AddSubgroup V)
    (h0 : (R : Set V) ∈ 𝓝 (0 : V)) {C : Set V} (hC : IsCompact C) (hRC : (R : Set V) ⊆ C) :
    ∃ μ : Measure V, μ.IsAddHaarMeasure ∧ SigmaFinite μ ∧ μ (R : Set V) = 1 := by sorry
