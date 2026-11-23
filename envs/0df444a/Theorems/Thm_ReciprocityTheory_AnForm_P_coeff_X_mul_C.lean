-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_P_coeff_X_mul_C
-- name    : ReciprocityTheory.AnForm.P.coeff_X_mul_C
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:47:44.761367+00:00
-- url     : https://prove2.me/theorems/43b3694f-149f-40de-a4c9-da675952649f
-- title:
--   P: coeff X mul C
-- statement:
--   The P construction uses the coeff X mul C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensA.lean#L107-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensA.lean#L107-L108

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

theorem ReciprocityTheory.AnForm.P.coeff_X_mul_C (a : ℂ) (n : ℕ) : (X * C a).coeff n = if n = 1 then a else 0 := by sorry
