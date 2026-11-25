-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_map_withDensity_integrable_integral
-- name    : ReciprocityTheory.AnForm.M.map_withDensity_integrable_integral
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:52:15.604521+00:00
-- url     : https://prove2.me/theorems/0032b175-7fbb-51b9-87d5-39f74d37a8d5
-- title:
--   M: map with Density integrable integral
-- statement:
--   The M construction uses the map with Density integrable integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/MaMeasureB.lean#L32-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/MaMeasureB.lean#L32-L55

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Set Filter Topology
open scoped ContDiff ENNReal NNReal
noncomputable section

theorem ReciprocityTheory.AnForm.M.map_withDensity_integrable_integral {e : ℕ} {X : Type} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {T : Set (Fin e → ℂ)} (hT : IsOpen T)
    {s : (Fin e → ℂ) → X} (hs : ContinuousOn s T) {w : (Fin e → ℂ) → ℝ} (hw : ContinuousOn w T)
    (hw0 : ∀ y ∈ T, 0 ≤ w y) {g : X → ℝ} (hg : Measurable g) :
    (Integrable g (((volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)).map s) ↔
      IntegrableOn (fun y => g (s y) * w y) T) ∧
    ∫ x, g x ∂(((volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)).map s) =
      ∫ y in T, g (s y) * w y := by sorry
