-- Prove2me | Theorems.Thm_TenChallenges_challenge_06_r0
-- name    : TenChallenges.challenge_06_r0
-- status  : Open
-- author  : @utkuokur
-- created : 2026-11-04T21:25:59.589189+00:00
-- url     : https://prove2.me/theorems/6706ff6c-f6ce-4f50-85cf-e89b7fe6475b
-- title:
--   Finite planar graphs are well-quasi-ordered by the minor relation
-- statement:
--   **The rung $r=0$ of Challenge 6: finite planar graphs are well-quasi-ordered under minors.** For every sequence $G_0,G_1,\dots$ of finite graphs without $K_5$ or $K_{3,3}$ minor there are indices $i<j$ such that $G_i$ is a minor of $G_j$:
--
--   $$\forall (G_n)_{n\in\mathbb N}\ \text{planar}:\quad \exists i<j:\ G_i\preceq G_j .$$
-- source:
--   N. Robertson, P. D. Seymour, Graph minors. XX. Wagner's conjecture, JCTB 92 (2004), 325–357, https://doi.org/10.1016/j.jctb.2004.08.001 (the planar case is a special case of the Graph Minor Theorem)

import Definitions.Def_TenChallenges_Challenge_06

namespace TenChallenges
theorem challenge_06_r0 : statement_06 0 := by sorry
end TenChallenges
