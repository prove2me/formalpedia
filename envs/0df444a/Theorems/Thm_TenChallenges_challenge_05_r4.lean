-- Prove2me | Theorems.Thm_TenChallenges_challenge_05_r4
-- name    : TenChallenges.challenge_05_r4
-- status  : Proved
-- author  : @utkuokur
-- created : 2026-11-04T21:29:38.596291+00:00
-- url     : https://prove2.me/theorems/432d6ebf-f581-409f-9604-f440afa7930b
-- title:
--   Erdős–Hajnal for the four-vertex path
-- statement:
--   **The rung $r=4$ of the Erdős–Hajnal conjecture for paths.** There is a constant $c>0$ such that every finite graph with no induced four-vertex path has a clique or an independent set of size at least $n^{c}$:
--
--   $$\exists c>0\ \ \forall G\ P_4\text{-free}:\quad \max(\omega(G),\alpha(G))\ \ge\ n^{c}.$$
--
--   The $P_4$-free graphs are the cographs; they are perfect, which gives $c=\tfrac12$.
-- source:
--   Standard: $P_4$-free graphs (cographs) are perfect, D. Seinsche, On a property of the class of n-colorable graphs, JCTB 16 (1974), https://doi.org/10.1016/0095-8956(74)90063-X; perfection gives $\omega(G)\alpha(G)\ge n$, so one of them is at least $\sqrt n$. Surveyed in M. Chudnovsky, The Erdős–Hajnal conjecture: a survey, JGT 75 (2014), Section 2.

import Definitions.Def_TenChallenges_Challenge_05

namespace TenChallenges
theorem challenge_05_r4 : statement_05 4 := by sorry
end TenChallenges
