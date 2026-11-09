-- Prove2me | Theorems.Thm_TenChallenges_frankl_pair_member
-- name    : TenChallenges.frankl_pair_member
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T03:34:52.574983+00:00
-- url     : https://prove2.me/theorems/d6cd5907-36d3-4d7f-86de-8902bc497e96
-- title:
--   Frankl's Conjecture for Families Containing a Pair
-- statement:
--   If a finite union-closed family contains a two-element set {x,y}, then at least one of x and y belongs to at least half of the members of the family.
-- source:
--   Ten Challenges in Combinatorics, Challenge 9; supporting lemma. https://tenchallenges.github.io/ten-challenges/

import Definitions.Def_TenChallenges_Challenge_09

namespace TenChallenges
theorem frankl_pair_member {U : Type*} [DecidableEq U] (F : Finset (Finset U))
    (huc : IsUnionClosed F) {x y : U} (hxy : x ≠ y)
    (hpair : ({x, y} : Finset U) ∈ F) :
    (1 / 2 : ℚ) ≤ density F x ∨ (1 / 2 : ℚ) ≤ density F y := by sorry
end TenChallenges
