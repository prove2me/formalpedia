-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_finrank_Kn
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.finrank_Kn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:55:13.020054+00:00
-- url     : https://prove2.me/theorems/1759cfad-a853-4960-bd33-d9fdc27166a0
-- title:
--   Local Class Field: finrank Kn
-- statement:
--   The Local Class Field construction uses the finrank Kn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtC.lean#L117-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtC.lean#L117-L121

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 Polynomial
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.finrank_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    Module.finrank ℚ_[p] (Kn p K n) = n * Module.finrank ℚ_[p] K := by sorry
