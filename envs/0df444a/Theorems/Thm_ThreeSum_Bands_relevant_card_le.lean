-- Prove2me | Theorems.Thm_ThreeSum_Bands_relevant_card_le
-- name    : ThreeSum.Bands.relevant_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:00:33.552726+00:00
-- url     : https://prove2.me/theorems/fb96d303-6174-4a70-b213-b1eb2615afa0
-- title:
--   Bands: relevant card le
-- statement:
--   Exact O(m²) bound, allowing different numbers of bands on each side.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Bands.lean#L149-L160
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Bands.lean#L149-L160

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

theorem ThreeSum.Bands.relevant_card_le [Fintype I] [Fintype J] [Fintype K]
    {alo ahi : I → ℤ} {blo bhi : J → ℤ} {clo chi : K → ℤ}
    (hA : Separated alo ahi) (hB : Separated blo bhi) (hC : Separated clo chi) :
    Fintype.card {p : I × (J × K) // Relevant alo ahi blo bhi clo chi p} ≤
      Fintype.card J * Fintype.card K +
        Fintype.card I * (Fintype.card J + Fintype.card K) := by sorry
