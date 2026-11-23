-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_P_cf_apply
-- name    : ReciprocityTheory.AnForm.P.cf_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:47:40.268185+00:00
-- url     : https://prove2.me/theorems/2772030d-3c12-490c-a54b-1f2b028ec6c0
-- title:
--   P: cf apply
-- statement:
--   The P construction uses the cf apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensA.lean#L92-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensA.lean#L92-L93

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

theorem ReciprocityTheory.AnForm.P.cf_apply {α β : Type*} (n : ℕ) (P : Matrix α β ℂ[X]) (i : α) (j : β) :
    cf n P i j = (P i j).coeff n := by sorry
