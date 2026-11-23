-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_abRestrict_toAb_eq_one_iff
-- name    : ReciprocityTheory.DiscreteGroups.GlobalClassField.abRestrict_toAb_eq_one_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:44.908329+00:00
-- url     : https://prove2.me/theorems/dfec28f3-3888-4b31-b786-3713a2abebd2
-- title:
--   Global Class Field: ab Restrict to Ab eq one iff
-- statement:
--   The Global Class Field construction uses the ab Restrict to Ab eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/AsGabLim.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/AsGabLim.lean#L51-L54

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

theorem ReciprocityTheory.DiscreteGroups.GlobalClassField.abRestrict_toAb_eq_one_iff (h : IsFiniteAbelian F L) (g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    abRestrict F L h (toAb F g) = 1 ↔ g ∈ L.fixingSubgroup := by sorry
