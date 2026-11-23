-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_locDens_unionAtlas_castAdd
-- name    : ReciprocityTheory.AnForm.M.locDens_unionAtlas_castAdd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:38:50.142101+00:00
-- url     : https://prove2.me/theorems/07b2f4e1-9450-4d6d-9e0a-7e36821cd45f
-- title:
--   M: loc Dens union Atlas cast Add
-- statement:
--   The M construction uses the loc Dens union Atlas cast Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/AtlasIndep.lean#L111-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/AtlasIndep.lean#L111-L115

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

theorem ReciprocityTheory.AnForm.M.locDens_unionAtlas_castAdd (A B : FinHolAtlas e X) (h : A.Compatible B)
    (Φ : Fin e → LocPot X) (j : Fin A.n) :
    locDens (unionAtlas A B h) Φ (Fin.castAdd B.n j) = locDens A Φ j := by sorry
