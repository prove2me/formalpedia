-- Prove2me | Theorems.Thm_TenChallenges_challenge_05_r6
-- name    : TenChallenges.challenge_05_r6
-- status  : Open
-- author  : @utkuokur
-- created : 2026-11-04T21:30:12.060889+00:00
-- url     : https://prove2.me/theorems/864e1ca9-f2a2-4e44-8af0-ea1ceea43f10
-- title:
--   Erdős–Hajnal for the six-vertex path
-- statement:
--   **The rung $r=6$ of the Erdős–Hajnal conjecture for paths.** There is a constant $c>0$ such that every finite graph with no induced six-vertex path has a clique or an independent set of size at least $n^{c}$:
--
--   $$\exists c>0\ \ \forall G\ P_6\text{-free}:\quad \max(\omega(G),\alpha(G))\ \ge\ n^{c}.$$
--
--   This rung is open.
-- source:
--   Open. The near-polynomial bound $2^{(\log n)^{d}}$ for every $d<1$ is T. Nguyen, A. Scott, P. Seymour, Induced subgraph density. V. All paths approach Erdős–Hajnal, https://arxiv.org/abs/2307.15032

import Definitions.Def_TenChallenges_Challenge_05

namespace TenChallenges
theorem challenge_05_r6 : statement_05 6 := by sorry
end TenChallenges
