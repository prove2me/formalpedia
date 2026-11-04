-- Prove2me | Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run
-- name    : ThreeSum.TernarySourceExecutionFactory.Ready.run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:26:06.124119+00:00
-- url     : https://prove2.me/theorems/d6fbbfe8-40c1-4352-a651-ab20b2e3432b
-- title:
--   Ready: run
-- statement:
--   This is an execution theorem for the literal SourceHost program, obtained
--   solely from its pure readiness certificate and the actual source kernels.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySourceExecutionFactory.lean#L120-L160
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySourceExecutionFactory.lean#L120-L160

import Definitions.Def_Submission_ThreeSum_LightTernarySourceCountHost
import Definitions.Def_Submission_ThreeSum_TernarySourceExecutionFactory
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernarySourceExecutionFactory
open Light LightSubsetAddress LightTernarySourceHost

theorem ThreeSum.TernarySourceExecutionFactory.Ready.run {N : ℕ} {S : Setup} {lim : Limits} {d : ℕ} {μ : ℕ→ℤ}
    {weight : ℕ→ℤ} {enumeration : ℕ→TernaryJointType.TritWord N}
    (H : Ready S lim d μ weight enumeration) :
    Meets lim (LightTernarySourceHost.program S.xs S.ys S.zs) 34 d S.argv μ S.runtime
      (fun _ ν => Kept μ ν S.base0 ∧ LightTernarySourceCountHost.BankReads
        ν S.valueBase S.groups S.bank (fun g r => S.values enumeration weight g (enumeration r))) := by sorry
