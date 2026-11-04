-- Prove2me | Theorems.Thm_ThreeSum_LightExtensionFactorSearch_nohit_all
-- name    : ThreeSum.LightExtensionFactorSearch.nohit_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:05:51.84893+00:00
-- url     : https://prove2.me/theorems/bcbea5d8-4822-4e42-88bc-c33c5fe217aa
-- title:
--   Light Extension Factor Search: nohit all
-- statement:
--   With a code range covering all bounded coefficient vectors, no hit
--   means no proper monic factor pair at this degree, with no residual code cutoff.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionFactorSearch.lean#L74-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionFactorSearch.lean#L74-L85

import Definitions.Def_Submission_ThreeSum_LightExtensionFactorPredicate
import Definitions.Def_Submission_ThreeSum_LightPairSearchProgram
import Definitions.Def_Submission_ThreeSum_LightExtensionFactorSearch
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightExtensionFactorSearch
open Light LightExtensionFactorPredicate
set_option maxHeartbeats 1000000
variable {lim : Limits}
attribute [local instance] ThreeSum.LightExtensionFactorSearch._p2m_local_instance_9c16afeb32_9

theorem ThreeSum.LightExtensionFactorSearch.nohit_all (C : Layout) (f : ℕ → ℕ) (q : ℕ) (hq : 0<q)
    (hp : 1≤C.p) (he : C.degree≤C.dim) (hcodes : C.p^C.dim≤q) :
    LightPairSearch.first (LightPairSearch.goodCode q (good C f)) (q*q)=0 ↔
      ∀ u v, ¬good C f u v := by sorry
