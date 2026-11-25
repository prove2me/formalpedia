-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_P_levi_eq_lines
-- name    : ReciprocityTheory.AnForm.P.levi_eq_lines
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:58.751216+00:00
-- url     : https://prove2.me/theorems/639ffe25-35b1-4d24-9f73-3b4f03b759d0
-- title:
--   P: levi eq lines
-- statement:
--   The P construction uses the levi eq lines property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensA.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensA.lean#L61-L66

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

theorem ReciprocityTheory.AnForm.P.levi_eq_lines {ι : Type*} [Fintype ι] {φ : (ι → ℂ) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (w : ι → ℂ) :
    levi φ 0 w = (deriv (deriv (fun s : ℝ => φ (s • w))) 0 +
      deriv (deriv (fun s : ℝ => φ (s • (Complex.I • w)))) 0) / 4 := by sorry
