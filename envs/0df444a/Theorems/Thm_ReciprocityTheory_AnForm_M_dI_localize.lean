-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_dI_localize
-- name    : ReciprocityTheory.AnForm.M.dI_localize
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:20:07.829392+00:00
-- url     : https://prove2.me/theorems/953e0851-d349-4f26-9087-71719876983f
-- title:
--   M: d I localize
-- statement:
--   The M construction uses the d I localize property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeIntA.lean#L112-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeIntA.lean#L112-L143

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

theorem ReciprocityTheory.AnForm.M.dI_localize (A : FinHolAtlas e X) (P : ChartPartition A)
    {D : Fin A.n → (Fin e → ℂ) → ℝ} (hD : DIChartDens A D) (k : Fin A.n) (g : X → ℝ)
    (hg : ∀ x, x ∉ (A.chart k).source → g x = 0)
    (hint : IntegrableOn (fun z => g ((A.chart k).symm z) * D k z) (A.chart k).target) :
    (∀ j, IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * D j y)
      (A.chart j).target) ∧
    ∑ j, ∫ y in (A.chart j).target, P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * D j y =
      ∫ z in (A.chart k).target, g ((A.chart k).symm z) * D k z := by sorry
