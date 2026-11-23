-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_dI_chi_contOn
-- name    : ReciprocityTheory.AnForm.M.dI_chi_contOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:21.69624+00:00
-- url     : https://prove2.me/theorems/ba8dac4e-35f0-450e-bb9a-145d5ffbfb9e
-- title:
--   M: d I chi cont On
-- statement:
--   The M construction uses the d I chi cont On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeIntA.lean#L95-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeIntA.lean#L95-L98

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntA
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
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem ReciprocityTheory.AnForm.M.dI_chi_contOn (A : FinHolAtlas e X) (P : ChartPartition A) (j k : Fin A.n) :
    ContinuousOn (fun y => P.χ j ((A.chart k).symm y)) (A.chart k).target := by sorry
