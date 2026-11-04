-- Prove2me | Theorems.Thm_ThreeSum_BlockEncoding_outputSubset_card
-- name    : ThreeSum.BlockEncoding.outputSubset_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:57.300235+00:00
-- url     : https://prove2.me/theorems/7581d352-def4-426c-845a-8a085b287d42
-- title:
--   Block Encoding: output Subset card
-- statement:
--   The Block Encoding construction uses the output Subset card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L49-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L49-L51

import Definitions.Def_Submission_ThreeSum_BlockRows
import Definitions.Def_Submission_ThreeSum_RawPrefixCounts
import Definitions.Def_Submission_ThreeSum_BlockEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.BlockEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows

theorem ThreeSum.BlockEncoding.outputSubset_card {h J : ℕ} (q : GlobalOutput h J) :
    (outputSubset q).card = J * (2 * h) := by sorry
