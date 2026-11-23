-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic
-- name    : ReciprocityTheory.AnForm.levi_re_analytic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:09.412344+00:00
-- url     : https://prove2.me/theorems/d7539e06-567f-476c-a3d7-afb6d8c464ea
-- title:
--   An Form: levi re analytic
-- statement:
--   The An Form construction uses the levi re analytic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PshShiftA.lean#L106-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PshShiftA.lean#L106-L124

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open Filter Topology
open scoped ContDiff
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem ReciprocityTheory.AnForm.levi_re_analytic {G : (ι → ℂ) → ℂ} {z : ι → ℂ} (hG : AnalyticAt ℂ G z) (w : ι → ℂ) :
    levi (fun y => (G y).re) z w = 0 := by sorry
