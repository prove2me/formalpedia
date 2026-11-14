-- Prove2me | Theorems.Thm_TenChallenges_challenge_09_r1
-- name    : TenChallenges.challenge_09_r1
-- status  : Proved
-- author  : @utkuokur
-- created : 2026-11-04T20:47:42.23839+00:00
-- url     : https://prove2.me/theorems/36966fb5-c320-495e-bc44-59aee94d594c
-- title:
--   An element of density at least $1/6$
-- statement:
--   **The rung $r=1$ of the scaled union-closed sets conjecture.** Every finite union-closed family $\mathcal F$ of finite sets with $\mathcal F\ne\emptyset$ and $\mathcal F\ne\{\emptyset\}$ has an element of density at least $\tfrac12-\tfrac13$:
--
--   $$\exists x:\quad \delta_{\mathcal F}(x)\ \ge\ \frac16 .$$
-- source:
--   Follows from the bound $\frac{3-\sqrt5}{2}$: Z. Chase, S. Lovett, Approximate union closed conjecture, https://arxiv.org/abs/2211.11689; W. Sawin, https://arxiv.org/abs/2211.11504; R. Alweiss, B. Huang, M. Sellke, https://arxiv.org/abs/2211.11731; L. Pebody, https://arxiv.org/abs/2211.13139

import Definitions.Def_TenChallenges_Challenge_09

namespace TenChallenges
theorem challenge_09_r1 : statement_09 1 := by sorry
end TenChallenges
