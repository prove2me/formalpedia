-- Prove2me | Theorems.Thm_ThreeSum_LightExtensionBackendLayout_budget
-- name    : ThreeSum.LightExtensionBackendLayout.budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:57:50.532462+00:00
-- url     : https://prove2.me/theorems/22a2bb15-6859-49f2-8be3-da0789da271c
-- title:
--   Light Extension Backend Layout: budget
-- statement:
--   The Light Extension Backend Layout construction uses the budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionBackendLayout.lean#L77-L176
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionBackendLayout.lean#L77-L176

import Definitions.Def_Submission_ThreeSum_LightExtensionBackend
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuBudget
import Definitions.Def_Submission_ThreeSum_LightIrreducibleBudget
import Definitions.Def_Submission_ThreeSum_LightExtensionBackendLayout
set_option autoImplicit false
open ThreeSum ThreeSum.LightExtensionBackendLayout
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
variable {lim : Limits}

theorem ThreeSum.LightExtensionBackendLayout.budget (base d p q J : ℕ) (hp : 1<p) (hd : 0<d) (hq : p^d=q)
    (hw : (lim.space : ℤ)≤lim.word)
    (hspace : base+reserve d p q J≤lim.space) :
    LightExtensionBackend.Budget lim (factor base d p q J)
      q (ctx base d) (ctx base d) (table base d) (logical base d q) (physical base d q J) J
      (a base d q J) (b base d q J) (h base d q J) (r base d q J) (prod base d q J) (sum base d q J)
      (LightIrreducibleFinder.uniformFactorTime d p q) := by sorry
