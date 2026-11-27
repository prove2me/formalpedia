-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_isOpen_abRestrict_fiber
-- name    : ReciprocityTheory.DiscreteGroups.GlobalClassField.isOpen_abRestrict_fiber
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:26:49.675693+00:00
-- url     : https://prove2.me/theorems/c357f0d6-b648-4c5b-bcc7-dd6886f93abc
-- title:
--   Global Class Field: is Open ab Restrict fiber
-- statement:
--   The Global Class Field construction uses the is Open ab Restrict fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/AsGabLimB.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/AsGabLimB.lean#L35-L37

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_AsGabLim
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_AsGabLimB
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
variable {F : Type*} [Field F] {L : IntermediateField F (AlgebraicClosure F)}

theorem ReciprocityTheory.DiscreteGroups.GlobalClassField.isOpen_abRestrict_fiber (h : IsFiniteAbelian F L) (τ : L ≃ₐ[F] L) :
    IsOpen {x : Field.absoluteGaloisGroupAbelianization F | abRestrict F L h x = τ} := by sorry
