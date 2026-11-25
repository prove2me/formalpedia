-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_card_characters_of_finite_quotient
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.card_characters_of_finite_quotient
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:52:21.637486+00:00
-- url     : https://prove2.me/theorems/d8738b1a-d7d0-4d9b-a0c7-f1fc71141939
-- title:
--   Local Class Field: card characters of finite quotient
-- statement:
--   The Local Class Field construction uses the card characters of finite quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/RecAbA.lean#L148-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/RecAbA.lean#L148-L158

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.card_characters_of_finite_quotient [Finite A] (hπ : Surjective π) :
    Nat.card {χ : charGrp G // ∀ g : G, π (Additive.ofMul g) = 0 → χ.1 (Additive.ofMul g) = 0} = Nat.card A := by sorry
