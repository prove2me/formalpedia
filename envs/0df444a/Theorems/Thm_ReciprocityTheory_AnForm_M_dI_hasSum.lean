-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_dI_hasSum
-- name    : ReciprocityTheory.AnForm.M.dI_hasSum
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:20:12.455866+00:00
-- url     : https://prove2.me/theorems/8759dc14-cc04-41a1-834f-e94d7fb128f4
-- title:
--   M: d I has Sum
-- statement:
--   The M construction uses the d I has Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeIntA.lean#L191-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeIntA.lean#L191-L237

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

theorem ReciprocityTheory.AnForm.M.dI_hasSum [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (P : ChartPartition A)
    (Φ : Fin e → LocPot X) (G : X → ℝ)
    (hG : ∀ j, IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * G ((A.chart j).symm y) *
      locDens A Φ j y) (A.chart j).target)
    (E : ℕ → Set X) (hE : ∀ m, MeasurableSet (E m)) (hd : Pairwise (Function.onFun Disjoint E))
    (N : Set X) (hN : ∀ j, volume ((A.chart j) '' (N ∩ (A.chart j).source)) = 0)
    (hcov : (⋃ m, E m) = Nᶜ) :
    HasSum (fun m => integralWith A P Φ ((E m).indicator G)) (integralWith A P Φ G) := by sorry
