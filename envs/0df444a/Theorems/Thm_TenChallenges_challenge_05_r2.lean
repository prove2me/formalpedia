-- Prove2me | Theorems.Thm_TenChallenges_challenge_05_r2
-- name    : TenChallenges.challenge_05_r2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:19:37.691921+00:00
-- url     : https://prove2.me/theorems/fde2e9cd-f24e-4689-afe0-78808ff2a5a9
-- title:
--   Erdős–Hajnal for paths: The path on two vertices
-- statement:
--   Every finite graph containing no induced path on two vertices has an independent set containing all its vertices. In particular, the two-vertex path satisfies the Erdős–Hajnal assertion with exponent one.
-- source:
--   Elementary special case / supporting lemma for Challenge 05. Definitions: https://tenchallenges.github.io/ten-challenges/#problems

import Definitions.Def_TenChallenges_Challenge_05
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
open SimpleGraph

theorem TenChallenges.challenge_05_r2 : TenChallenges.statement_05 2 := by sorry
