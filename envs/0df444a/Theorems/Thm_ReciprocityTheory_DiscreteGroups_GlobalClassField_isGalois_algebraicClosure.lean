-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_isGalois_algebraicClosure
-- name    : ReciprocityTheory.DiscreteGroups.GlobalClassField.isGalois_algebraicClosure
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:56.803963+00:00
-- url     : https://prove2.me/theorems/d6b91843-eac9-4187-855e-de75e0e56bb0
-- title:
--   Global Class Field: is Galois algebraic Closure
-- statement:
--   The Global Class Field construction uses the is Galois algebraic Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/AsGabLim.lean#L56-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/AsGabLim.lean#L56-L56

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

theorem ReciprocityTheory.DiscreteGroups.GlobalClassField.isGalois_algebraicClosure [CharZero F] : IsGalois F (AlgebraicClosure F) := by sorry
