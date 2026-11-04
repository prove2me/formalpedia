-- Prove2me | Theorems.Thm_ThreeSum_Bands_overlapOwner_injective
-- name    : ThreeSum.Bands.overlapOwner_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:22:28.546574+00:00
-- url     : https://prove2.me/theorems/e22c8a6b-3688-46d3-a2a2-02bd1c1bff19
-- title:
--   Bands: overlap Owner injective
-- statement:
--   The Bands construction uses the overlap Owner injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Bands.lean#L52-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Bands.lean#L52-L78

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sets
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Bands
set_option autoImplicit false
open ThreeSum ThreeSum.Bands
variable {I J K : Type*}

theorem ThreeSum.Bands.overlapOwner_injective {alo ahi : I → ℤ} {blo bhi : J → ℤ}
    (hA : Separated alo ahi) (hB : Separated blo bhi)
    {p q : I × J} (hp : Overlap alo ahi blo bhi p) (hq : Overlap alo ahi blo bhi q)
    (heq : overlapOwner alo blo p = overlapOwner alo blo q) : p = q := by sorry
