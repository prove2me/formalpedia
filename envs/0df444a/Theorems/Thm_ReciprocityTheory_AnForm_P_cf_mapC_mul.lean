-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_P_cf_mapC_mul
-- name    : ReciprocityTheory.AnForm.P.cf_mapC_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:47:17.061076+00:00
-- url     : https://prove2.me/theorems/07f5663f-1d41-46d8-9dbd-21afb82ab23a
-- title:
--   P: cf map C mul
-- statement:
--   The P construction uses the cf map C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensA.lean#L102-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensA.lean#L102-L105

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

theorem ReciprocityTheory.AnForm.P.cf_mapC_mul {α β γ : Type*} [Fintype β] (n : ℕ) (A : Matrix α β ℂ)
    (P : Matrix β γ ℂ[X]) : cf n (A.map C * P) = A * cf n P := by sorry
