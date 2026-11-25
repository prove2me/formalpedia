-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_sum_le_of_le
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.norm_sum_le_of_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:51:41.207803+00:00
-- url     : https://prove2.me/theorems/76c3cea0-dc46-4baf-a444-aafe79cb175e
-- title:
--   Unramified Extensions: norm sum le of le
-- statement:
--   The Unramified Extensions construction uses the norm sum le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtB.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtB.lean#L14-L16

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Definitions.Def_Lemmata_GeneralBFactUpperTerForm_Imports
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
open ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
variable {p}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.norm_sum_le_of_le {ι : Type} (s : Finset ι) (g : ι → PadicAlgCl p) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ j ∈ s, ‖g j‖ ≤ C) : ‖∑ j ∈ s, g j‖ ≤ C := by sorry
