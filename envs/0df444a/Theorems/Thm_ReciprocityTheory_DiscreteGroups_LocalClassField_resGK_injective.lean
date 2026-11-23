-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_resGK_injective
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.resGK_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:54:37.274986+00:00
-- url     : https://prove2.me/theorems/2d7eea8a-003f-4ebd-89dc-a4aa21ccd9ed
-- title:
--   Local Class Field: res GK injective
-- statement:
--   The Local Class Field construction uses the res GK injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L153-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L153-L154

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K L}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.resGK_injective (h : K ≤ L) : Injective (resGK h) := by sorry
