-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_qK_le_pow_finrank
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.qK_le_pow_finrank
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:50.61078+00:00
-- url     : https://prove2.me/theorems/857ae960-aa79-42d5-b95b-4369c8627cc1
-- title:
--   Local Class Field: q K le pow finrank
-- statement:
--   The Local Class Field construction uses the q K le pow finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtB.lean#L128-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtB.lean#L128-L134

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.qK_le_pow_finrank (hK : FiniteDimensional ℚ_[p] K) {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hL : FiniteDimensional ℚ_[p] L) (hKL : K ≤ L) :
    ∃ f : ℕ, 0 < f ∧ qK p L = qK p K ^ f ∧ f * Module.finrank ℚ_[p] K ≤ Module.finrank ℚ_[p] L := by sorry
