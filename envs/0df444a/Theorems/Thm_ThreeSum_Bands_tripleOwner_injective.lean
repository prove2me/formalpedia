-- Prove2me | Theorems.Thm_ThreeSum_Bands_tripleOwner_injective
-- name    : ThreeSum.Bands.tripleOwner_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:11:01.59202+00:00
-- url     : https://prove2.me/theorems/fcce5e04-57fe-401e-bccd-acd53b405c7c
-- title:
--   Bands: triple Owner injective
-- statement:
--   The Bands construction uses the triple Owner injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Bands.lean#L106-L146
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Bands.lean#L106-L146

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

theorem ThreeSum.Bands.tripleOwner_injective
    {alo ahi : I → ℤ} {blo bhi : J → ℤ} {clo chi : K → ℤ}
    (hA : Separated alo ahi) (hB : Separated blo bhi) (hC : Separated clo chi)
    {p q : I × (J × K)} (hp : Relevant alo ahi blo bhi clo chi p)
    (hq : Relevant alo ahi blo bhi clo chi q)
    (heq : tripleOwner alo blo bhi clo p = tripleOwner alo blo bhi clo q) : p = q := by sorry
