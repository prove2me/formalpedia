-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_eK_dvd_of_le
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.eK_dvd_of_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:52:38.188903+00:00
-- url     : https://prove2.me/theorems/d81eb2ba-c1c4-51af-9025-8625bb750a64
-- title:
--   Local Class Field: e K dvd of le
-- statement:
--   The Local Class Field construction uses the e K dvd of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsC.lean#L84-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsC.lean#L84-L86

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {K L}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.eK_dvd_of_le (h : K ≤ L) : eK p K ∣ eK p L := by sorry
