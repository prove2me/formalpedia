-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_ResCompat_unique
-- name    : ReciprocityTheory.DiscreteGroups.GlobalClassField.ResCompat.unique
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:27:35.375833+00:00
-- url     : https://prove2.me/theorems/504d3da6-febd-543a-9373-f67838c9c37d
-- title:
--   Res Compat: unique
-- statement:
--   The Res Compat construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/AsGabLim.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/AsGabLim.lean#L14-L18

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_AsGabLim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.GlobalClassField
open _root_.Neutral.B1 Topology Function
open scoped commutatorElement
variable {F : Type*} [Field F] {L L' : IntermediateField F (AlgebraicClosure F)}

theorem ReciprocityTheory.DiscreteGroups.GlobalClassField.ResCompat.unique {hle : L ≤ L'} {τ' : L' ≃ₐ[F] L'} {τ₁ τ₂ : L ≃ₐ[F] L}
    (h₁ : ResCompat hle τ' τ₁) (h₂ : ResCompat hle τ' τ₂) : τ₁ = τ₂ := by sorry
