-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_P_leviForm_half_log_abs_of_fderiv_eq_zero
-- name    : ReciprocityTheory.AnForm.P.leviForm_half_log_abs_of_fderiv_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:40.067877+00:00
-- url     : https://prove2.me/theorems/5c14f8e7-e440-41d4-9251-39ac4cdbb060
-- title:
--   P: levi Form half log abs of fderiv eq zero
-- statement:
--   The P construction uses the levi Form half log abs of fderiv eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensA.lean#L11-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensA.lean#L11-L37

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open Filter Topology Polynomial Matrix
open scoped ContDiff
noncomputable section

theorem ReciprocityTheory.AnForm.P.leviForm_half_log_abs_of_fderiv_eq_zero {ι : Type} [Fintype ι] (f : (ι → ℂ) → ℝ) (z : ι → ℂ)
    (hf : ContDiffAt ℝ 2 f z) (hz : f z ≠ 0) (hd : fderiv ℝ f z = 0) (w : ι → ℂ) :
    levi (fun x => (1 / 2) * Real.log |f x|) z w = levi f z w / (2 * f z) := by sorry
