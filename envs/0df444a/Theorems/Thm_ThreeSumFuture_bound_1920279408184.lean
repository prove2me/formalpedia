-- Prove2me | Theorems.Thm_ThreeSumFuture_bound_1920279408184
-- name    : ThreeSumFuture.bound_1920279408184
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T07:33:19.55183+00:00
-- url     : https://prove2.me/theorems/4db85669-fd72-452b-a677-11e22b76bab4
-- title:
--   Open target: deterministic 3SUM in $O(n^{1.920279408184})$ time
-- statement:
--   Open improvement target: for every fixed natural magnitude exponent κ, find one finite deterministic word-RAM program, a word-width constant and a time function with exponent 240034926023/125000000000 = 1.920279408184, uniformly deciding whether three distinct positions sum to zero for every input size, every input bounded in magnitude by n^κ and every word width above the specified logarithmic bound. This is the unchanged campaign predicate at a slightly smaller exponent. No proof of this stronger target is claimed by the cited baseline.
-- source:
--   https://prove2.me/campaigns/3sum-exponent

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem ThreeSumFuture.bound_1920279408184 :
    EndStatement.ThreeSum.SolvedInTime 1.920279408184 := by sorry
