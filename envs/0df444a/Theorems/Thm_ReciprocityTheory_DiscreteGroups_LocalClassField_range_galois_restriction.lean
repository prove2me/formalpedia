-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_range_galois_restriction
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.range_galois_restriction
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:02:16.311365+00:00
-- url     : https://prove2.me/theorems/79018b51-09e1-42ca-bd66-b10ada5d8f52
-- title:
--   Local Class Field: range galois restriction
-- statement:
--   The Local Class Field construction uses the range galois restriction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L105-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L105-L111

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.range_galois_restriction (h : K ≤ L) : (resGK h).range = subG p K L := by sorry
