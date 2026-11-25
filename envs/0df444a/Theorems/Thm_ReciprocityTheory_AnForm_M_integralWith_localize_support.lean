-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_integralWith_localize_support
-- name    : ReciprocityTheory.AnForm.M.integralWith_localize_support
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:20:09.38428+00:00
-- url     : https://prove2.me/theorems/07fdea5a-5edf-52d6-a31d-fa76d5d0f680
-- title:
--   M: integral With localize support
-- statement:
--   The M construction uses the integral With localize support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeInt.lean#L14-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeInt.lean#L14-L58

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeInt
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
variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem ReciprocityTheory.AnForm.M.integralWith_localize_support [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (P : ChartPartition A) (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (k : Fin A.n) (g : X → ℝ) (hg : ∀ x, x ∉ (A.chart k).source → g x = 0)
    (hint : IntegrableOn (fun z => g ((A.chart k).symm z) * locDens A Φ k z)
      (A.chart k).target) :
    (∀ j, IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) *
      locDens A Φ j y) (A.chart j).target) ∧
    integralWith A P Φ g = ∫ z in (A.chart k).target, g ((A.chart k).symm z) * locDens A Φ k z := by sorry
