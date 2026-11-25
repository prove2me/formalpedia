-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_span_singleton_OK
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.mem_span_singleton_OK
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:38:28.465784+00:00
-- url     : https://prove2.me/theorems/e3d81e5d-4550-5cfc-aee0-3678a7b1ab64
-- title:
--   Local Class Field: mem span singleton OK
-- statement:
--   The Local Class Field construction uses the mem span singleton OK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsD.lean#L69-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsD.lean#L69-L90

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.mem_span_singleton_OK (a b : OK p K) :
    a ∈ Ideal.span {b} ↔ ‖((a : K) : PadicAlgCl p)‖ ≤ ‖((b : K) : PadicAlgCl p)‖ := by sorry
