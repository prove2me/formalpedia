-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_GK
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.norm_GK
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:58.096773+00:00
-- url     : https://prove2.me/theorems/7a04749d-b9c9-4881-96ae-4be83755f77f
-- title:
--   Unramified Extensions: norm GK
-- statement:
--   The Unramified Extensions construction uses the norm GK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormSubEqOneOfPowEqOne.lean#L63-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormSubEqOneOfPowEqOne.lean#L63-L64

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrDefs
import Definitions.Def_Lemmata_PadicNatCastNorm_NormNatCastOfNotDvd
import Definitions.Def_Lemmata_FirstBlockLemmaC_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaD_Imports
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormSubEqOneOfPowEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField
variable {p : ℕ} [Fact p.Prime]

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.norm_GK {K : IntermediateField ℚ_[p] (PadicAlgCl p)} (σ : GK p K) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ := by sorry
