-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_abRestrict_ext
-- name    : ReciprocityTheory.DiscreteGroups.GlobalClassField.abRestrict_ext
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:27:32.923943+00:00
-- url     : https://prove2.me/theorems/45e6bd7b-bd43-51d2-a67b-4ddce41f5b1b
-- title:
--   Global Class Field: ab Restrict ext
-- statement:
--   The Global Class Field construction uses the ab Restrict ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/AsGabLim.lean#L114-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/AsGabLim.lean#L114-L118

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

theorem ReciprocityTheory.DiscreteGroups.GlobalClassField.abRestrict_ext [CharZero F] {x y : Field.absoluteGaloisGroupAbelianization F}
    (hxy : ∀ (L : IntermediateField F (AlgebraicClosure F)) (h : IsFiniteAbelian F L),
      abRestrict F L h x = abRestrict F L h y) : x = y := by sorry
