-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_hom_QZ_ne_zero
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.exists_hom_QZ_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:02.675747+00:00
-- url     : https://prove2.me/theorems/cdc83db4-fda8-4d5f-976f-948e9dc994b4
-- title:
--   Local Class Field: exists hom QZ ne zero
-- statement:
--   The Local Class Field construction uses the exists hom QZ ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/RecAbA.lean#L95-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/RecAbA.lean#L95-L100

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_QZDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecAbA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 Function
noncomputable section
variable (A : Type) [AddCommGroup A] [Finite A]
variable {A}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.exists_hom_QZ_ne_zero {a : A} (ha : a ≠ 0) : ∃ χ : A →+ QZ, χ a ≠ 0 := by sorry
