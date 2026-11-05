-- Prove2me | Theorems.Thm_TenChallenges_challenge_06_r2
-- name    : TenChallenges.challenge_06_r2
-- status  : Open
-- author  : @utkuokur
-- created : 2026-11-04T21:26:43.232774+00:00
-- url     : https://prove2.me/theorems/7bf3b980-adfc-4b02-832c-95c6193849e4
-- title:
--   Finite planar graphs are $1$-well-quasi-ordered by the minor relation
-- statement:
--   **The rung $r=2$ of Challenge 6: finite planar graphs are $1$-well-quasi-ordered under minors.** For every sequence $X_0,X_1,\dots$ of nonempty sets of finite planar graphs there are indices $i<j$ such that every graph in $X_i$ is a minor of some graph in $X_j$:
--
--   $$\forall (X_n)_{n\in\mathbb N}:\quad \exists i<j\ \ \forall G\in X_i\ \ \exists H\in X_j:\ G\preceq H .$$
--
--   Here $2=2\cdot 1+0$, so the level is $\alpha=1$ and the class is the planar graphs.
-- source:
--   Open; context in A. Georgakopoulos, On better-quasi-ordering under graph minors, https://arxiv.org/abs/2510.19285

import Definitions.Def_TenChallenges_Challenge_06

namespace TenChallenges
theorem challenge_06_r2 : statement_06 2 := by sorry
end TenChallenges
