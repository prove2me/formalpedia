-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_measurable_gt
-- name    : ReciprocityTheory.L2DbarEstimates.I.ap_measurable_gt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:58:27.172676+00:00
-- url     : https://prove2.me/theorems/8fe50790-3701-407c-8ef3-4331da68ec8e
-- title:
--   I: ap measurable gt
-- statement:
--   The I construction uses the ap measurable gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyB.lean#L112-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyB.lean#L112-L126

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff Classical

theorem ReciprocityTheory.L2DbarEstimates.I.ap_measurable_gt {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
    (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (ph : M → ℝ)
    (r : ℝ) (c : M → ℂ) (W : M → Set M) (m : ℝ)
    (hS : (zeroSet n g).Finite) (hW : IsLocalData n g ph r W m) :
    Measurable (gt n z g c W) := by sorry
