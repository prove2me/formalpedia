-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_bound_1920279408185
-- name    : WeightedCache3SUMRefinement.bound_1920279408185
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T07:28:36.785809+00:00
-- url     : https://prove2.me/theorems/73b990cc-cf9a-4e7f-ba93-f9fb8159a2ac
-- title:
--   Deterministic weighted-cache 3SUM in $O(n^{1.920279408185})$ time
-- statement:
--   For every fixed natural magnitude exponent κ, there exist one finite deterministic word-RAM program, a word-width constant and a time function with exponent 384055881637/200000000000 = 1.920279408185, uniformly deciding whether three distinct positions sum to zero for every input size, every input bounded in magnitude by n^κ and every word width above the specified logarithmic bound. This is the unchanged 3SUM campaign predicate and the exact end statement exported by the pinned source.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission.lean#L8-L10

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem WeightedCache3SUMRefinement.bound_1920279408185 :
    EndStatement.ThreeSum.SolvedInTime 1.920279408185 := by sorry
