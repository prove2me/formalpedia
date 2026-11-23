-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_dI_target_of_weights
-- name    : ReciprocityTheory.AnForm.M.dI_target_of_weights
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:57.580058+00:00
-- url     : https://prove2.me/theorems/3eabe0cb-a719-4675-9309-45ae24e3d589
-- title:
--   M: d I target of weights
-- statement:
--   The M construction uses the d I target of weights property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeIntA.lean#L145-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeIntA.lean#L145-L158

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

theorem ReciprocityTheory.AnForm.M.dI_target_of_weights (A : FinHolAtlas e X) (P : ChartPartition A)
    {D : Fin A.n → (Fin e → ℂ) → ℝ} (hD : DIChartDens A D) (g : X → ℝ)
    (hw : ∀ j, IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) *
      D j y) (A.chart j).target) (k : Fin A.n) :
    IntegrableOn (fun y => g ((A.chart k).symm y) * D k y) (A.chart k).target := by sorry
