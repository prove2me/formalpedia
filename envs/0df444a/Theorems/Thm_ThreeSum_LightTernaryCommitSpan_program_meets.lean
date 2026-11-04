-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryCommitSpan_program_meets
-- name    : ThreeSum.LightTernaryCommitSpan.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:22:21.279252+00:00
-- url     : https://prove2.me/theorems/78c370ca-f420-44c8-b315-b266ea8103ef
-- title:
--   Light Ternary Commit Span: program meets
-- statement:
--   The selected expanded digit-span catalog is copied back into the fixed
--   old catalog. Both reserved catalog buffers can therefore have fixed pointers
--   through every prefix, with only their actual row count increasing.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCommitSpan.lean#L12-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCommitSpan.lean#L12-L30

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryCommitSpan
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCommitSpan
open Light

theorem ThreeSum.LightTernaryCommitSpan.program_meets {lim : Limits} {oldCatalog newCatalog J rows d : ℕ}
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ)≤lim.word)
    (hApart : oldCatalog+rows*J≤newCatalog)
    (hSpace : newCatalog+rows*J≤lim.space) :
    Meets lim program 0 d [newCatalog,oldCatalog,rows*J] μ (time J rows)
      (fun _ ν => (∀ k<rows, ∀ i<J,
          ν (oldCatalog+J*k+i)=μ (newCatalog+J*k+i)) ∧
        SameOutside μ ν oldCatalog (rows*J)) := by sorry
