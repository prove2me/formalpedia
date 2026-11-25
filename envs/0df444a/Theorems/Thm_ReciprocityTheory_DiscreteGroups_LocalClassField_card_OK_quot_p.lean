-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_card_OK_quot_p
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.card_OK_quot_p
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:38:24.70891+00:00
-- url     : https://prove2.me/theorems/2f1a77fb-e35e-5337-b579-08e0436c25c0
-- title:
--   Local Class Field: card OK quot p
-- statement:
--   The Local Class Field construction uses the card OK quot p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsD.lean#L52-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsD.lean#L52-L62

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.card_OK_quot_p (hK : FiniteDimensional ℚ_[p] K) :
    Nat.card (OK p K ⧸ Ideal.span {(p : OK p K)}) = p ^ Module.finrank ℚ_[p] K := by sorry
