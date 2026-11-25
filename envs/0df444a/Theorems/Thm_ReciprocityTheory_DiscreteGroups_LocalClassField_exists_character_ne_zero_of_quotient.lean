-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_character_ne_zero_of_quotient
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.exists_character_ne_zero_of_quotient
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:52:52.046655+00:00
-- url     : https://prove2.me/theorems/3dc98115-8b6e-4009-ba53-58fbe51f826a
-- title:
--   Local Class Field: exists character ne zero of quotient
-- statement:
--   The Local Class Field construction uses the exists character ne zero of quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/RecAbA.lean#L143-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/RecAbA.lean#L143-L146

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.exists_character_ne_zero_of_quotient [Finite A] (g : G) (hg : π (Additive.ofMul g) ≠ 0) :
    ∃ χ : charGrp G, (∀ g : G, π (Additive.ofMul g) = 0 → χ.1 (Additive.ofMul g) = 0) ∧ χ.1 (Additive.ofMul g) ≠ 0 := by sorry
