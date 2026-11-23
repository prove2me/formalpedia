-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_residue_eq_iff
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.residue_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:26.86151+00:00
-- url     : https://prove2.me/theorems/d1fbf737-4a07-46f8-aa92-8d0054791976
-- title:
--   Local Class Field: residue eq iff
-- statement:
--   The Local Class Field construction uses the residue eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtA.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtA.lean#L13-L16

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.residue_eq_iff (x y : Obar p) :
    IsLocalRing.residue (Obar p) x = IsLocalRing.residue (Obar p) y ↔
      ‖(x : PadicAlgCl p) - (y : PadicAlgCl p)‖ < 1 := by sorry
