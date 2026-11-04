-- Prove2me | Theorems.Thm_ThreeSum_BlockForced_residual_injective
-- name    : ThreeSum.BlockForced.residual_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:12:37.247116+00:00
-- url     : https://prove2.me/theorems/d57ed324-bb51-4163-a334-b351fbc17019
-- title:
--   Block Forced: residual injective
-- statement:
--   The Block Forced construction uses the residual injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockForced.lean#L182-L188
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockForced.lean#L182-L188

import Definitions.Def_Submission_ThreeSum_BlockEncoding
import Definitions.Def_Submission_ThreeSum_BlockForced
set_option autoImplicit false
open ThreeSum ThreeSum.BlockForced
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding

theorem ThreeSum.BlockForced.residual_injective {h J : ℕ} (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h))) :
    Set.InjOn (residual (h := h) I) (↑(completedTuples q I u) : Set (ChoiceTuple h J)) := by sorry
