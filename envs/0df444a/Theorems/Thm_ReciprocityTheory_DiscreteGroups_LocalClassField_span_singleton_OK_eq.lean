-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_span_singleton_OK_eq
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.span_singleton_OK_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:47:07.787987+00:00
-- url     : https://prove2.me/theorems/2c28a2e9-7fd2-44b0-8a92-ac9ba3f38a87
-- title:
--   Local Class Field: span singleton OK eq
-- statement:
--   The Local Class Field construction uses the span singleton OK eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsD.lean#L92-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsD.lean#L92-L95

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.span_singleton_OK_eq {a b : OK p K} (h : ‖((a : K) : PadicAlgCl p)‖ = ‖((b : K) : PadicAlgCl p)‖) :
    Ideal.span {a} = Ideal.span {b} := by sorry
