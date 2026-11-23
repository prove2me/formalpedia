-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_subG_normal_of_le
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.subG_normal_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:54:52.100059+00:00
-- url     : https://prove2.me/theorems/7bdb98a1-395a-4521-ab30-77bbc56f2b87
-- title:
--   Local Class Field: sub G normal of le
-- statement:
--   The Local Class Field construction uses the sub G normal of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L149-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L149-L151

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.subG_normal_of_le {K' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ K') (hL : K ≤ L)
    (hn : (subG p K L).Normal) : (subG p K' L).Normal := by sorry
