-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_P_hasDerivAt_line
-- name    : ReciprocityTheory.AnForm.P.hasDerivAt_line
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:10.7468+00:00
-- url     : https://prove2.me/theorems/109a5e27-5750-47cc-b5aa-917cf22be3c7
-- title:
--   P: has Deriv At line
-- statement:
--   The P construction uses the has Deriv At line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensA.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensA.lean#L39-L43

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

theorem ReciprocityTheory.AnForm.P.hasDerivAt_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {φ : E → ℝ}
    {v : E} {t : ℝ} (h : DifferentiableAt ℝ φ (t • v)) :
    HasDerivAt (fun s : ℝ => φ (s • v)) (fderiv ℝ φ (t • v) v) t := by sorry
