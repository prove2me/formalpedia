-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_ResCompat_inv
-- name    : ReciprocityTheory.DiscreteGroups.GlobalClassField.ResCompat.inv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:27:43.063283+00:00
-- url     : https://prove2.me/theorems/0ef675ea-a149-40a7-9b7b-0800ef0bfeb1
-- title:
--   Res Compat: inv
-- statement:
--   The Res Compat construction uses the inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/AsGabLim.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/AsGabLim.lean#L40-L47

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

theorem ReciprocityTheory.DiscreteGroups.GlobalClassField.ResCompat.inv {hle : L ≤ L'} {τ' : L' ≃ₐ[F] L'} {τ : L ≃ₐ[F] L}
    (h : ResCompat hle τ' τ) : ResCompat hle τ'⁻¹ τ⁻¹ := by sorry
