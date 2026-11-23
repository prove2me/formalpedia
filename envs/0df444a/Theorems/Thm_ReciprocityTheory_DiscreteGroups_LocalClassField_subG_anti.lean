-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_subG_anti
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.subG_anti
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:54:45.879735+00:00
-- url     : https://prove2.me/theorems/dee5cde1-8928-4cfb-9f92-3141361fb752
-- title:
--   Local Class Field: sub G anti
-- statement:
--   The Local Class Field construction uses the sub G anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L22-L23

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.subG_anti {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : L ≤ L') : subG p K L' ≤ subG p K L := by sorry
