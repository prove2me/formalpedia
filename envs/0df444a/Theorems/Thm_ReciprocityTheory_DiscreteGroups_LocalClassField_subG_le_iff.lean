-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_subG_le_iff
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.subG_le_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:54:59.930354+00:00
-- url     : https://prove2.me/theorems/fa41cb02-6f65-497b-b66f-e9967970aa42
-- title:
--   Local Class Field: sub G le iff
-- statement:
--   The Local Class Field construction uses the sub G le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L50-L58

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.subG_le_iff {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ L) :
    subG p K L' ≤ subG p K L ↔ L ≤ K ⊔ L' := by sorry
