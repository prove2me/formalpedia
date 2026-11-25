-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_mem_closure_commutator_iff
-- name    : ReciprocityTheory.DiscreteGroups.GlobalClassField.mem_closure_commutator_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:51:46.888422+00:00
-- url     : https://prove2.me/theorems/10de945f-5a0e-4bdb-b6e5-1f2ba0b87f85
-- title:
--   Global Class Field: mem closure commutator iff
-- statement:
--   The Global Class Field construction uses the mem closure commutator iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/AsGabLim.lean#L78-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/AsGabLim.lean#L78-L106

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

theorem ReciprocityTheory.DiscreteGroups.GlobalClassField.mem_closure_commutator_iff [CharZero F] (g : Field.absoluteGaloisGroup F) :
    g ∈ (commutator (Field.absoluteGaloisGroup F)).topologicalClosure ↔
      ∀ L : IntermediateField F (AlgebraicClosure F), IsFiniteAbelian F L → g ∈ L.fixingSubgroup := by sorry
