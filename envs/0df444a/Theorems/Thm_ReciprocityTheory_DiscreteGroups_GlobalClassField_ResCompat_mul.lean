-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_ResCompat_mul
-- name    : ReciprocityTheory.DiscreteGroups.GlobalClassField.ResCompat.mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:51:54.043017+00:00
-- url     : https://prove2.me/theorems/d99650ab-8607-482d-85a8-a1ebcdfd821a
-- title:
--   Res Compat: mul
-- statement:
--   The Res Compat construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/AsGabLim.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/AsGabLim.lean#L22-L25

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

theorem ReciprocityTheory.DiscreteGroups.GlobalClassField.ResCompat.mul {hle : L ≤ L'} {σ' τ' : L' ≃ₐ[F] L'} {σ τ : L ≃ₐ[F] L}
    (h₁ : ResCompat hle σ' σ) (h₂ : ResCompat hle τ' τ) : ResCompat hle (σ' * τ') (σ * τ) := by sorry
