-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_holoOn_of_compatible
-- name    : ReciprocityTheory.AnForm.M.holoOn_of_compatible
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:45.213616+00:00
-- url     : https://prove2.me/theorems/b6706871-5c47-5fdb-a728-439e6fa161d4
-- title:
--   M: holo On of compatible
-- statement:
--   The M construction uses the holo On of compatible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/AtlasIndep.lean#L75-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/AtlasIndep.lean#L75-L83

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

theorem ReciprocityTheory.AnForm.M.holoOn_of_compatible {A B : FinHolAtlas e X} (h : A.Compatible B) {U : Set X}
    (hU : IsOpen U) {g : X → ℂ} (hg : A.HoloOn U g) : B.HoloOn U g := by sorry
