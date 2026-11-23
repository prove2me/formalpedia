-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_P_deriv_re_eval
-- name    : ReciprocityTheory.AnForm.P.deriv_re_eval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:08.447526+00:00
-- url     : https://prove2.me/theorems/af1dc2a6-3aff-4caf-9a7a-a32b0d85e704
-- title:
--   P: deriv re eval
-- statement:
--   The P construction uses the deriv re eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensA.lean#L74-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensA.lean#L74-L77

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

theorem ReciprocityTheory.AnForm.P.deriv_re_eval (D : ℂ[X]) :
    deriv (fun s : ℝ => (D.eval (s : ℂ)).re) = fun s : ℝ => (D.derivative.eval (s : ℂ)).re := by sorry
