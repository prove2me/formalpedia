-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_integralWith_extendRight
-- name    : ReciprocityTheory.AnForm.M.integralWith_extendRight
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:53.191448+00:00
-- url     : https://prove2.me/theorems/d15f04cc-9e67-4146-a518-6d447afe90f6
-- title:
--   M: integral With extend Right
-- statement:
--   The M construction uses the integral With extend Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/AtlasIndep.lean#L240-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/AtlasIndep.lean#L240-L246

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AtlasIndep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem ReciprocityTheory.AnForm.M.integralWith_extendRight [CompactSpace X] [T2Space X] {A B : FinHolAtlas e X}
    (h : A.Compatible B) (Q : ChartPartition B) (Φ : Fin e → LocPot X) (g : X → ℝ) :
    integralWith (unionAtlas A B h) (Q.extendRight h) Φ g = integralWith B Q Φ g := by sorry
