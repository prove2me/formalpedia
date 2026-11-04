-- Prove2me | Theorems.Thm_ThreeSum_BlockEncoding_tuple_eq_of_output_leftSubset
-- name    : ThreeSum.BlockEncoding.tuple_eq_of_output_leftSubset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:16:47.112147+00:00
-- url     : https://prove2.me/theorems/75f5dfa9-75c8-4ee2-822c-d7f47a3195d8
-- title:
--   Block Encoding: tuple eq of output left Subset
-- statement:
--   The occurrence and union tuple together with the left subset determine
--   both endpoints, including all schedule multiplicity tags.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L76-L86
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L76-L86

import Definitions.Def_Submission_ThreeSum_BlockRows
import Definitions.Def_Submission_ThreeSum_RawPrefixCounts
import Definitions.Def_Submission_ThreeSum_BlockEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.BlockEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows

theorem ThreeSum.BlockEncoding.tuple_eq_of_output_leftSubset {h J : ℕ} {s t : ChoiceTuple h J}
    (hq : tupleOutput s = tupleOutput t) (hL : leftSubset s = leftSubset t) : s = t := by sorry
