-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_valuation_intCast_le_one_local_class_field
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.valuation_intCast_le_one_local_class_field
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:01:25.181418+00:00
-- url     : https://prove2.me/theorems/7716dddd-00d7-4bd6-99f6-8c29b60dfe9b
-- title:
--   Local Class Field: valuation int Cast le one local class field
-- statement:
--   The Local Class Field construction uses the valuation int Cast le one local class field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/TransportA.lean#L78-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/TransportA.lean#L78-L79

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_TransportDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_TransportA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ValuativeRel Function Filter Topology
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]
  (p : ℕ) [Fact p.Prime]

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.valuation_intCast_le_one_local_class_field (n : ℤ) : valuation K (n : K) ≤ 1 := by sorry
