-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_sigBar_red
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.sigBar_red
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:35.447877+00:00
-- url     : https://prove2.me/theorems/26bc936b-ce60-4e06-8bd5-e8fc8a34b74e
-- title:
--   Unramified Extensions: sig Bar red
-- statement:
--   The Unramified Extensions construction uses the sig Bar red property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/PowPowSuccSub.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/PowPowSuccSub.lean#L28-L29

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemOfPowQKSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField Polynomial
variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.sigBar_red (σ : GK p K) {x : PadicAlgCl p} (hx : ‖x‖ ≤ 1) : sigBar σ (red x) = red (σ x) := by sorry
