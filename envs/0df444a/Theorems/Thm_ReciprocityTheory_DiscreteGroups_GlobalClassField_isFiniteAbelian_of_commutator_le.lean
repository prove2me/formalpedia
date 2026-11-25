-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_isFiniteAbelian_of_commutator_le
-- name    : ReciprocityTheory.DiscreteGroups.GlobalClassField.isFiniteAbelian_of_commutator_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:51:37.206435+00:00
-- url     : https://prove2.me/theorems/09f57ddc-5518-4097-9ab3-2aea77f3446f
-- title:
--   Global Class Field: is Finite Abelian of commutator le
-- statement:
--   The Global Class Field construction uses the is Finite Abelian of commutator le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/AsGabLim.lean#L58-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/AsGabLim.lean#L58-L76

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

theorem ReciprocityTheory.DiscreteGroups.GlobalClassField.isFiniteAbelian_of_commutator_le [CharZero F] (hfd : FiniteDimensional F L)
    (hc : commutator (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) ≤ L.fixingSubgroup) :
    IsFiniteAbelian F L := by sorry
