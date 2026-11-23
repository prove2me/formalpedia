-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_isPotential_of_compatible
-- name    : ReciprocityTheory.AnForm.M.isPotential_of_compatible
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:39:08.520211+00:00
-- url     : https://prove2.me/theorems/ee77e43e-a636-48cc-b263-ab004e25a44b
-- title:
--   M: is Potential of compatible
-- statement:
--   The M construction uses the is Potential of compatible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/AtlasIndep.lean#L85-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/AtlasIndep.lean#L85-L89

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

theorem ReciprocityTheory.AnForm.M.isPotential_of_compatible {A B : FinHolAtlas e X} (h : A.Compatible B) {P : LocPot X}
    (hP : IsPotential A P) : IsPotential B P := by sorry
