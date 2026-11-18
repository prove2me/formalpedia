-- Prove2me | Theorems.Thm_TenChallenges_challenge_06_all_graphs
-- name    : TenChallenges.challenge_06_all_graphs
-- status  : Open
-- author  : @Davide
-- created : 2026-11-17T10:46:09.466204+00:00
-- url     : https://prove2.me/theorems/5246ba69-c7ca-4db9-b62f-d3d28b1d736c
-- title:
--   Finite graphs are $\alpha$-WQO under minors for every ordinal $\alpha$
-- statement:
--   **The better-quasi-ordering conjecture for graph minors, for all finite graphs.** For every ordinal $\alpha$, the class of finite simple graphs is $\alpha$-well-quasi-ordered by the minor relation $\preceq$:
--
--   $$\forall\,\alpha\in\mathrm{Ord}:\quad (V^*_\alpha(\mathcal G_{\mathrm{fin}}),\le^*)\ \text{is well-quasi-ordered}.$$
--
--   This is the odd-rung half of the Challenge 6 goal, $\mathrm{WQO}(2\alpha+1)$ for every $\alpha$. The case $\alpha=0$ is the Robertson-Seymour Graph Minor Theorem; every case $\alpha\ge1$ is open. Since better-quasi-ordering is $\alpha$-WQO for every $\alpha$, this is equivalent to the folklore conjecture that finite graphs are BQO under minors. The planar half of the goal follows from this statement because $\alpha$-WQO passes to subclasses.
-- source:
--   Ten Challenges 06 mission statement (folklore BQO conjecture for graph minors; see Georgakopoulos 2025, https://arxiv.org/abs/2510.19285). Odd rungs r = 2·α + 1 of TenChallenges.statement_06.

import Definitions.Def_TenChallenges_AlphaWQO

namespace TenChallenges
theorem challenge_06_all_graphs : ∀ α : Ordinal, IsAlphaWQO FiniteGraph.MinorLE α := by sorry
end TenChallenges
