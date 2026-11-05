-- Prove2me | Theorems.Thm_TenChallenges_challenge_06
-- name    : TenChallenges.challenge_06
-- status  : Open
-- author  : @utkuokur
-- created : 2026-11-04T21:25:43.838988+00:00
-- url     : https://prove2.me/theorems/3230ca7b-621a-4e0b-ac99-2ce11d2427cd
-- title:
--   Finite graphs are $\alpha$-well-quasi-ordered under minors for every ordinal $\alpha$
-- statement:
--   **Better-quasi-ordering of finite graphs under minors**, in the scaled form of Challenge 6. For every ordinal $r$, writing $r=2\cdot\alpha+k$ with $k\in\{0,1\}$: if $k=0$, the finite planar graphs are $\alpha$-well-quasi-ordered under the minor relation; if $k=1$, all finite graphs are $\alpha$-well-quasi-ordered under the minor relation:
--
--   $$\forall\,\alpha\in\mathrm{Ord}:\quad (\mathcal G_{\mathrm{planar}},\preceq)\text{ and }(\mathcal G_{\mathrm{fin}},\preceq)\text{ are }\alpha\text{-WQO}.$$
--
--   Since better-quasi-ordering is $\alpha$-well-quasi-ordering for every $\alpha$, the statement is the folklore conjecture that finite graphs are better-quasi-ordered by the minor relation. The cases $\alpha=0$ are the Graph Minor Theorem; every case $\alpha\ge 1$ is open.
--
--   **Formalization Note.** The statement is `∀ r : Ordinal, statement_06 r`.
-- source:
--   Folklore conjecture, stated as Conjecture 1.1 in A. Georgakopoulos, On better-quasi-ordering under graph minors, https://arxiv.org/abs/2510.19285; scaled form in V. Bajpai, N. Bowler, J. Carmesin, U. Okur, 10 Scalable Challenges in Combinatorics, AI4Math @ CICM 2026, challenge 6

import Definitions.Def_TenChallenges_Challenge_06

namespace TenChallenges
theorem challenge_06 : ∀ r : Ordinal, statement_06 r := by sorry
end TenChallenges
