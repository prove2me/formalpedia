-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_isOpen_ker_abRestrict
-- name    : ReciprocityTheory.DiscreteGroups.GlobalClassField.isOpen_ker_abRestrict
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:58:16.24745+00:00
-- url     : https://prove2.me/theorems/8e8027e6-9019-4a99-90a4-bfca8569100b
-- title:
--   Global Class Field: is Open ker ab Restrict
-- statement:
--   The Global Class Field construction uses the is Open ker ab Restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/AsGabLimB.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/AsGabLimB.lean#L23-L33

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

theorem ReciprocityTheory.DiscreteGroups.GlobalClassField.isOpen_ker_abRestrict (h : IsFiniteAbelian F L) :
    IsOpen ((abRestrict F L h).ker : Set (Field.absoluteGaloisGroupAbelianization F)) := by sorry
