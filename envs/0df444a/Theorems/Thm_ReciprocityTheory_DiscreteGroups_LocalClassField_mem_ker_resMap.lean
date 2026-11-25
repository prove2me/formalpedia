-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_ker_resMap
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.mem_ker_resMap
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:38:21.504155+00:00
-- url     : https://prove2.me/theorems/d34cb85b-2914-596d-8283-2d4e7c5b96e0
-- title:
--   Local Class Field: mem ker res Map
-- statement:
--   The Local Class Field construction uses the mem ker res Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsD.lean#L102-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsD.lean#L102-L107

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.mem_ker_resMap (x : OK p K) : x ∈ RingHom.ker (resMap p K) ↔ ‖((x : K) : PadicAlgCl p)‖ < 1 := by sorry
