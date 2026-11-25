-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_model_of_algebra
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.exists_model_of_algebra
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:53:47.514302+00:00
-- url     : https://prove2.me/theorems/689bb3a6-75fc-5f74-a80a-c044c9930931
-- title:
--   Local Class Field: exists model of algebra
-- statement:
--   The Local Class Field construction uses the exists model of algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/TransportA.lean#L220-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/TransportA.lean#L220-L240

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.exists_model_of_algebra (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] [ContinuousSMul ℚ_[p] K] :
    ∃ m : Model K p, ∀ x : ℚ_[p], (m.e (algebraMap ℚ_[p] K x) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) x := by sorry
