-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_P_zMat_smul
-- name    : ReciprocityTheory.AnForm.P.zMat_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:14.226273+00:00
-- url     : https://prove2.me/theorems/ad3ed3da-baba-4e2c-b23c-7934d9f780df
-- title:
--   P: z Mat smul
-- statement:
--   The P construction uses the z Mat smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensB.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensB.lean#L56-L59

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open Polynomial Matrix
noncomputable section

theorem ReciprocityTheory.AnForm.P.zMat_smul (N : ℕ) (z : Pairs N → ℂ) (c : ℂ) : zMat N (c • z) = c • zMat N z := by sorry
