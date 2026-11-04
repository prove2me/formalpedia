-- Prove2me | Theorems.Thm_ThreeSum_GlobalEncoding_mem_localFiber
-- name    : ThreeSum.GlobalEncoding.mem_localFiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:12:59.612242+00:00
-- url     : https://prove2.me/theorems/684cc3ba-16eb-41f6-a008-246f0ace7172
-- title:
--   Global Encoding: mem local Fiber
-- statement:
--   The Global Encoding construction uses the mem local Fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L100-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L100-L105

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_GlobalEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.GlobalEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments

theorem ThreeSum.GlobalEncoding.mem_localFiber {h : ℕ} (a b : ℤ) (c : RetainedChoice h) :
    c ∈ Radix.localFiber (localPrime h) rawLeft rawRight a b ↔
      HashFamily.hashValue (mapAt h (occurrence c)) (left (edge c)) = (a : LocalField h) ∧
      HashFamily.hashValue (mapAt h (occurrence c)) (right (edge c)) = (b : LocalField h) := by sorry
