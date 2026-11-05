-- Prove2me | Theorems.Thm_TenChallenges_excluded_minor_bound_mono
-- name    : TenChallenges.excluded_minor_bound_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:19:27.267876+00:00
-- url     : https://prove2.me/theorems/3c706ef8-4d23-43d7-b884-784d5c1ac58c
-- title:
--   Excluded minors for representability: Monotonicity of excluded-minor bounds
-- statement:
--   Suppose all positive prime powers at most r admit an excluded-minor bound B. The same assertion holds for every smaller range r′≤r and every larger bound B′≥B.
-- source:
--   Elementary special case / supporting lemma for Challenge 02. Definitions: https://tenchallenges.github.io/ten-challenges/#problems

import Definitions.Def_TenChallenges_Challenge_02

theorem TenChallenges.excluded_minor_bound_mono {r r' B B' : ℕ} (hr : r' ≤ r) (hB : B ≤ B')
    (h : TenChallenges.statement_02 r B) : TenChallenges.statement_02 r' B' := by sorry
