-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_P_zMat_real_smul
-- name    : ReciprocityTheory.AnForm.P.zMat_real_smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:37.694856+00:00
-- url     : https://prove2.me/theorems/8cff14ce-53fb-47b3-b810-b75788493d17
-- title:
--   P: z Mat real smul
-- statement:
--   The P construction uses the z Mat real smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensB.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensB.lean#L61-L64

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

theorem ReciprocityTheory.AnForm.P.zMat_real_smul (N : ℕ) (z : Pairs N → ℂ) (s : ℝ) :
    zMat N (s • z) = (s : ℂ) • zMat N z := by sorry
