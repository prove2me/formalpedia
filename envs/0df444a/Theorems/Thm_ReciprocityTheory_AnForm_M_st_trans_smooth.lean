-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_st_trans_smooth
-- name    : ReciprocityTheory.AnForm.M.st_trans_smooth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:01:18.004684+00:00
-- url     : https://prove2.me/theorems/950f12d1-76cf-470f-9ed0-26e6ad2535f6
-- title:
--   M: st trans smooth
-- statement:
--   The M construction uses the st trans smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesB.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesB.lean#L12-L15

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem ReciprocityTheory.AnForm.M.st_trans_smooth (A : FinHolAtlas e X) (j k : Fin A.n) :
    ContDiffOn ℝ ∞ (A.chart k ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source) := by sorry
