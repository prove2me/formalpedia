-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_normGroup_self_eq_top
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.normGroup_self_eq_top
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:54:51.167372+00:00
-- url     : https://prove2.me/theorems/68a3bb6e-68c7-5874-aed0-2de134f50a20
-- title:
--   Local Class Field: norm Group self eq top
-- statement:
--   The Local Class Field construction uses the norm Group self eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormOpenA.lean#L217-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormOpenA.lean#L217-L225

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormOpenA
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
variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.normGroup_self_eq_top : normGrp p K K = ⊤ := by sorry
