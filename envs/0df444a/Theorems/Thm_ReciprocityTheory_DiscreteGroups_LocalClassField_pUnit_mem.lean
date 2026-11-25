-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_pUnit_mem
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.pUnit_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:56:36.973868+00:00
-- url     : https://prove2.me/theorems/03e3ab53-d29c-52bf-ba98-89b169d9bebe
-- title:
--   Local Class Field: p Unit mem
-- statement:
--   The Local Class Field construction uses the p Unit mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsB.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsB.lean#L81-L83

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsB
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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.pUnit_mem : pUnit p ∈ multOf p K := by sorry
