-- Prove2me | Theorems.Thm_TenChallenges_frankl_singleton_member
-- name    : TenChallenges.frankl_singleton_member
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T22:51:18.100831+00:00
-- url     : https://prove2.me/theorems/140a75ab-acc6-4f80-af06-9793bddca4f2
-- title:
--   Frankl's Conjecture for Families Containing a Singleton
-- statement:
--   If a finite union-closed family $\mathcal{F}$ contains a singleton set $\{x\} \in \mathcal{F}$, then the element $x$ appears in at least half of the sets of $\mathcal{F}$, i.e., $\mathrm{density}(\mathcal{F}, x) \ge 1/2$.
-- source:
--   Ten Challenges in Combinatorics, Challenge 9 (Union-closed sets), https://tenchallenges.github.io/ten-challenges/

import Definitions.Def_TenChallenges_Challenge_09

namespace TenChallenges
theorem frankl_singleton_member {U : Type*} [DecidableEq U] (F : Finset (Finset U)) (huc : IsUnionClosed F) {x : U} (hx : ({x} : Finset U) ∈ F) : density F x ≥ 1 / 2 := by sorry
end TenChallenges
