-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_isOpen_fiber_of_isOpen_ker
-- name    : ReciprocityTheory.DiscreteGroups.GlobalClassField.isOpen_fiber_of_isOpen_ker
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:51:37.401234+00:00
-- url     : https://prove2.me/theorems/a3f873c0-f23c-5da9-9e7a-443191846827
-- title:
--   Global Class Field: is Open fiber of is Open ker
-- statement:
--   The Global Class Field construction uses the is Open fiber of is Open ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/AsGabLimB.lean#L9-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/AsGabLimB.lean#L9-L21

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

theorem ReciprocityTheory.DiscreteGroups.GlobalClassField.isOpen_fiber_of_isOpen_ker {A B : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [Group B]
    (φ : A →* B) (h : IsOpen (φ.ker : Set A)) (b : B) : IsOpen {a | φ a = b} := by sorry
