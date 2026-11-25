-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_UKi_iff
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.mem_UKi_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:59:30.558478+00:00
-- url     : https://prove2.me/theorems/15edc40a-0485-4474-9550-c91155bde26d
-- title:
--   Local Class Field: mem UKi iff
-- statement:
--   The Local Class Field construction uses the mem UKi iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsF.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsF.lean#L45-L46

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.mem_UKi_iff (i : ℕ) (x : Kˣ) :
    x ∈ UKi p K i ↔ x ∈ UK p K ∧ ‖((x : K) : PadicAlgCl p) - 1‖ ≤ (p : ℝ) ^ (- (i : ℝ) / eK p K) := by sorry
