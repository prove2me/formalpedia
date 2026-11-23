-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_comap_resGK_subG
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.comap_resGK_subG
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:16.508232+00:00
-- url     : https://prove2.me/theorems/5fc80500-7369-4145-b0ed-7923426bd494
-- title:
--   Local Class Field: comap res GK sub G
-- statement:
--   The Local Class Field construction uses the comap res GK sub G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L167-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L167-L170

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.comap_resGK_subG (h : K ≤ L) (L' : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    (subG p K L').comap (resGK h) = subG p L L' := by sorry
