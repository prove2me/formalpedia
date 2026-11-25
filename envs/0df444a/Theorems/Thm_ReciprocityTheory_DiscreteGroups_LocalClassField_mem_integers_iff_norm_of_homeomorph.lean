-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_integers_iff_norm_of_homeomorph
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.mem_integers_iff_norm_of_homeomorph
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:59:55.288921+00:00
-- url     : https://prove2.me/theorems/a2ceaab4-cf6a-5c2d-a7a0-a6c1d6a947d2
-- title:
--   Local Class Field: mem integers iff norm of homeomorph
-- statement:
--   The Local Class Field construction uses the mem integers iff norm of homeomorph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/TransportA.lean#L199-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/TransportA.lean#L199-L218

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.mem_integers_iff_norm_of_homeomorph {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {L : Type} [NormedField L] (e : K ≃+* L) (he : IsHomeomorph e) (x : K) :
    x ∈ 𝒪[K] ↔ ‖e x‖ ≤ 1 := by sorry
