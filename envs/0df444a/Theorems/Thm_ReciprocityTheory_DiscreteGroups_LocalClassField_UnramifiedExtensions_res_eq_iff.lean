-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_res_eq_iff
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.res_eq_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:28:26.418101+00:00
-- url     : https://prove2.me/theorems/31c79495-26a7-4288-b5c9-02f93b3ead83
-- title:
--   Unramified Extensions: res eq iff
-- statement:
--   The Unramified Extensions construction uses the res eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormSubEqOneOfPowEqOne.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormSubEqOneOfPowEqOne.lean#L51-L53

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.res_eq_iff (x y : Obar p) : res x = res y ↔ ‖(x : PadicAlgCl p) - (y : PadicAlgCl p)‖ < 1 := by sorry
