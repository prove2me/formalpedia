-- Prove2me | Theorems.Thm_PI_UnimodIdxWork_measure_subgroup_eq
-- name    : PI.UnimodIdxWork.measure_subgroup_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:30:59.636472+00:00
-- url     : https://prove2.me/theorems/fb7c75ac-82b8-4c59-9886-42f912c2e6c2
-- title:
--   Unimod Idx Work: measure subgroup eq
-- statement:
--   The Unimod Idx Work construction uses the measure subgroup eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularIndex/PairwiseDisjointCosets.lean#L74-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularIndex/PairwiseDisjointCosets.lean#L74-L105

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnimodIdx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularIndex_PairwiseDisjointCosets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Pointwise Set Function
noncomputable section
open PI PI.UnimodIdxWork
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]

theorem PI.UnimodIdxWork.measure_subgroup_eq (μ : Measure G) [IsMulLeftInvariant μ] (A H : Subgroup G)
    (hA : IsOpen (A : Set G)) (hH : IsCompact (H : Set G)) (hHo : IsOpen (H : Set G)) :
    μ H = (A.relIndex H : ENNReal) * μ (A ⊓ H : Subgroup G) := by sorry
