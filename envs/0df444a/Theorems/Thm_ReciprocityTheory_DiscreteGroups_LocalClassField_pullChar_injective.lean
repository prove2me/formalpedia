-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_pullChar_injective
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.pullChar_injective
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:54:22.39502+00:00
-- url     : https://prove2.me/theorems/85faa8e5-f019-44fe-a328-abb7b66a2011
-- title:
--   Local Class Field: pull Char injective
-- statement:
--   The Local Class Field construction uses the pull Char injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/RecAbA.lean#L130-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/RecAbA.lean#L130-L134

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.pullChar_injective (hπ : Surjective π) : Injective (pullChar π hc) := by sorry
