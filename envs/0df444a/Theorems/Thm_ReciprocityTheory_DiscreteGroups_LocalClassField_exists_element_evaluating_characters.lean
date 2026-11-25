-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_element_evaluating_characters
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.exists_element_evaluating_characters
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:53:01.612547+00:00
-- url     : https://prove2.me/theorems/a7ce217c-389c-49e3-8be8-539888819fb7
-- title:
--   Local Class Field: exists element evaluating characters
-- statement:
--   The Local Class Field construction uses the exists element evaluating characters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/RecAbA.lean#L160-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/RecAbA.lean#L160-L167

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_QZDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecAbA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 Function
noncomputable section
variable {G : Type} [Group G] [TopologicalSpace G] {A : Type} [AddCommGroup A] (π : Additive G →+ A)
  (hc : IsLocallyConstant fun g : G => π (Additive.ofMul g))
variable {π}
include hc

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.exists_element_evaluating_characters [Finite A] (hπ : Surjective π) (f : charGrp G →+ QZ) :
    ∃ g : G, ∀ χ : charGrp G, (∀ g : G, π (Additive.ofMul g) = 0 → χ.1 (Additive.ofMul g) = 0) →
      χ.1 (Additive.ofMul g) = f χ := by sorry
