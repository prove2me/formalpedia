-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_padic_hom_mem_integers_iff
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.padic_hom_mem_integers_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:08:02.601524+00:00
-- url     : https://prove2.me/theorems/2c62e7a8-5115-46f8-9a78-962040e65ad2
-- title:
--   Local Class Field: padic hom mem integers iff
-- statement:
--   The Local Class Field construction uses the padic hom mem integers iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/TransportA.lean#L172-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/TransportA.lean#L172-L195

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
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {p : ℕ} [Fact p.Prime]

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.padic_hom_mem_integers_iff (f : ℚ_[p] →+* K) (hf : Continuous f) (x : ℚ_[p]) :
    f x ∈ 𝒪[K] ↔ ‖x‖ ≤ 1 := by sorry
