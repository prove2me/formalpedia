-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_finrank_fun
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.finrank_fun
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:54:56.734798+00:00
-- url     : https://prove2.me/theorems/b71906c7-e3bf-4b14-84b6-e225e3d71caf
-- title:
--   Unramified Extensions: finrank fun
-- statement:
--   The Unramified Extensions construction uses the finrank fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtB.lean#L122-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtB.lean#L122-L124

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Definitions.Def_Lemmata_GeneralBFactUpperTerForm_Imports
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtB
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
open ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
variable {p} {K}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.finrank_fun (hK : FiniteDimensional ℚ_[p] K) (f : ℕ) : Module.finrank ℚ_[p] (Fin f → K) = f * Module.finrank ℚ_[p] K := by sorry
