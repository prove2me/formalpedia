-- Prove2me | Theorems.Thm_PI_OmFibreUniq_W_open_eq_countable_union
-- name    : PI.OmFibreUniq.W.open_eq_countable_union
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:15:51.893342+00:00
-- url     : https://prove2.me/theorems/7b195d3f-b6bb-412c-bd21-93fbfca45522
-- title:
--   W: open eq countable union
-- statement:
--   The W construction uses the open eq countable union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/UniqGen.lean#L27-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/UniqGen.lean#L27-L41

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
variable [SecondCountableTopology V]

theorem PI.OmFibreUniq.W.open_eq_countable_union {W : Set V} (hW : IsOpen W) :
    ∃ T : Set (Set V), T.Countable ∧ (∀ K ∈ T, IsCompact K ∧ IsOpen K ∧ K ⊆ W) ∧ ⋃₀ T = W := by sorry
