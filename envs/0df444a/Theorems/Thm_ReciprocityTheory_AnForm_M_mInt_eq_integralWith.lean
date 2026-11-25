-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_mInt_eq_integralWith
-- name    : ReciprocityTheory.AnForm.M.mInt_eq_integralWith
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:55:08.559662+00:00
-- url     : https://prove2.me/theorems/7caf1738-458e-4aec-ba04-844fe43271b3
-- title:
--   M: m Int eq integral With
-- statement:
--   The M construction uses the m Int eq integral With property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/MaMeasureB.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/MaMeasureB.lean#L26-L30

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

theorem ReciprocityTheory.AnForm.M.mInt_eq_integralWith {e : ℕ} {X : Type} [TopologicalSpace X]
    (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (hne : Nonempty (ChartPartition A))
    (g : X → ℝ) : mInt A Φ g = integralWith A hne.some Φ g := by sorry
