-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_dI_bdd_mul
-- name    : ReciprocityTheory.AnForm.M.dI_bdd_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:20:19.046889+00:00
-- url     : https://prove2.me/theorems/968a16ea-70fc-4dcc-911c-fc31b6eb519e
-- title:
--   M: d I bdd mul
-- statement:
--   The M construction uses the d I bdd mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeIntA.lean#L103-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeIntA.lean#L103-L110

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

theorem ReciprocityTheory.AnForm.M.dI_bdd_mul (A : FinHolAtlas e X) (P : ChartPartition A) (j k : Fin A.n)
    {f : (Fin e → ℂ) → ℝ} (hf : IntegrableOn f (A.chart k).target) :
    IntegrableOn (fun y => P.χ j ((A.chart k).symm y) * f y) (A.chart k).target := by sorry
