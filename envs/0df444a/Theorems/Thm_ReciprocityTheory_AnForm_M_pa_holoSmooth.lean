-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_pa_holoSmooth
-- name    : ReciprocityTheory.AnForm.M.pa_holoSmooth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:53.164581+00:00
-- url     : https://prove2.me/theorems/62c560d0-c231-4267-a41c-30aa1c12dd55
-- title:
--   M: pa holo Smooth
-- statement:
--   The M construction uses the pa holo Smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/Partition.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/Partition.lean#L11-L13

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff
noncomputable section

theorem ReciprocityTheory.AnForm.M.pa_holoSmooth {e e' : ℕ} (F : (Fin e → ℂ) → (Fin e' → ℂ)) (U : Set (Fin e → ℂ))
    (hF : AnalyticOnNhd ℂ F U) : ContDiffOn ℝ ∞ F U := by sorry
