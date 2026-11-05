-- Prove2me | Theorems.Thm_TenChallenges_challenge_05_r5
-- name    : TenChallenges.challenge_05_r5
-- status  : Open
-- author  : @utkuokur
-- created : 2026-11-04T21:29:48.764359+00:00
-- url     : https://prove2.me/theorems/a5910c8e-ccc6-42e8-a4de-60ccc9be194c
-- title:
--   Erdős–Hajnal for the five-vertex path
-- statement:
--   **The rung $r=5$ of the Erdős–Hajnal conjecture for paths** (Nguyen, Scott and Seymour). There is a constant $c>0$ such that every finite graph with no induced five-vertex path has a clique or an independent set of size at least $n^{c}$:
--
--   $$\exists c>0\ \ \forall G\ P_5\text{-free}:\quad \max(\omega(G),\alpha(G))\ \ge\ n^{c}.$$
-- source:
--   T. Nguyen, A. Scott, P. Seymour, Induced subgraph density. VII. The five-vertex path, Proc. London Math. Soc. (2026), https://arxiv.org/abs/2312.15333, Theorem 1.1

import Definitions.Def_TenChallenges_Challenge_05

namespace TenChallenges
theorem challenge_05_r5 : statement_05 5 := by sorry
end TenChallenges
