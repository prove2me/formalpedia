-- Prove2me | Theorems.Thm_TenChallenges_challenge_06_r1
-- name    : TenChallenges.challenge_06_r1
-- status  : Open
-- author  : @utkuokur
-- created : 2026-11-04T21:26:22.355088+00:00
-- url     : https://prove2.me/theorems/7e6ffd2b-ec17-4427-a2b3-dc52b018f5ed
-- title:
--   Finite graphs are well-quasi-ordered by the minor relation (Graph Minor Theorem)
-- statement:
--   **The rung $r=1$ of Challenge 6: the Graph Minor Theorem.** For every sequence $G_0,G_1,\dots$ of finite graphs there are indices $i<j$ such that $G_i$ is a minor of $G_j$:
--
--   $$\forall (G_n)_{n\in\mathbb N}:\quad \exists i<j:\ G_i\preceq G_j .$$
-- source:
--   N. Robertson, P. D. Seymour, Graph minors. XX. Wagner's conjecture, JCTB 92 (2004), 325–357, https://doi.org/10.1016/j.jctb.2004.08.001, Theorem 1.1 (the Graph Minor Theorem)

import Definitions.Def_TenChallenges_Challenge_06

namespace TenChallenges
theorem challenge_06_r1 : statement_06 1 := by sorry
end TenChallenges
