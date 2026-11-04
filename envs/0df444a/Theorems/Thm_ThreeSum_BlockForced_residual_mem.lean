-- Prove2me | Theorems.Thm_ThreeSum_BlockForced_residual_mem
-- name    : ThreeSum.BlockForced.residual_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:12:35.00614+00:00
-- url     : https://prove2.me/theorems/f37b17a9-a8b3-4f34-8f35-19fcfeaac43f
-- title:
--   Block Forced: residual mem
-- statement:
--   The Block Forced construction uses the residual mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockForced.lean#L172-L180
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockForced.lean#L172-L180

import Definitions.Def_Submission_ThreeSum_BlockEncoding
import Definitions.Def_Submission_ThreeSum_BlockForced
set_option autoImplicit false
open ThreeSum ThreeSum.BlockForced
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding

theorem ThreeSum.BlockForced.residual_mem {h J : ℕ} (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h)))
    (hu : ∀ i ∈ I, u i ⊆ outputRows q i) (t : ChoiceTuple h J)
    (ht : t ∈ completedTuples q I u) : residual I t ∈ admissibleResiduals q I u := by sorry
