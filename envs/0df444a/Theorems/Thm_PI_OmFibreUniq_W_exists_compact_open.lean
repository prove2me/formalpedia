-- Prove2me | Theorems.Thm_PI_OmFibreUniq_W_exists_compact_open
-- name    : PI.OmFibreUniq.W.exists_compact_open
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:15:52.865886+00:00
-- url     : https://prove2.me/theorems/3b53ea22-3f6f-59de-8fa0-b9331e0534c8
-- title:
--   W: exists compact open
-- statement:
--   The W construction uses the exists compact open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/UniqGen.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/UniqGen.lean#L16-L23

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_UniqGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W
open MeasureTheory Topology Set Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal
variable {V : Type} [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V]
  [TotallyDisconnectedSpace V]

theorem PI.OmFibreUniq.W.exists_compact_open {W : Set V} (hW : IsOpen W) {x : V} (hx : x ∈ W) :
    ∃ K, IsCompact K ∧ IsOpen K ∧ x ∈ K ∧ K ⊆ W := by sorry
