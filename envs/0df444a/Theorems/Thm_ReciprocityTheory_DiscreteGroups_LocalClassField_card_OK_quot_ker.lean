-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_card_OK_quot_ker
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.card_OK_quot_ker
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:44:48.41075+00:00
-- url     : https://prove2.me/theorems/fbe54144-96b8-558c-b8e5-7fe7c5ab40f8
-- title:
--   Local Class Field: card OK quot ker
-- statement:
--   The Local Class Field construction uses the card OK quot ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsD.lean#L109-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsD.lean#L109-L117

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelF
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Neutral.Cmp
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
attribute [local instance] zpAlgOK

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.card_OK_quot_ker : Nat.card (OK p K ⧸ RingHom.ker (resMap p K)) = qK p K := by sorry
