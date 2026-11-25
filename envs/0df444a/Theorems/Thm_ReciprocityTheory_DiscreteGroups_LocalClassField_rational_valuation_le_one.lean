-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_rational_valuation_le_one
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.rational_valuation_le_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:00:47.245067+00:00
-- url     : https://prove2.me/theorems/a2981137-0100-4bce-9d1b-ea8519c94c6a
-- title:
--   Local Class Field: rational valuation le one
-- statement:
--   The Local Class Field construction uses the rational valuation le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/TransportA.lean#L81-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/TransportA.lean#L81-L103

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.rational_valuation_le_one (hp : valuation K (p : K) < 1) (q : ℚ) (hq : Rat.padicValuation p q ≤ 1) :
    valuation K (q : K) ≤ 1 := by sorry
