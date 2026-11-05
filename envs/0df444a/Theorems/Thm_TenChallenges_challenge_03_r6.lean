-- Prove2me | Theorems.Thm_TenChallenges_challenge_03_r6
-- name    : TenChallenges.challenge_03_r6
-- status  : Open
-- author  : @utkuokur
-- created : 2026-11-04T21:34:48.564754+00:00
-- url     : https://prove2.me/theorems/fbd5c480-0163-43c3-8c33-92f5a2da94f9
-- title:
--   Caccetta–Häggkvist for $r = 6$
-- statement:
--   **The rung $r=6$ of the Caccetta–Häggkvist conjecture.** Every loopless digraph on $n\ge 1$ vertices in which every vertex has out-degree at least $6$ contains a directed cycle of length at most $\lceil n/6\rceil$:
--
--   $$\delta^+(D)\ge 6 \implies \text{girth}(D)\le\lceil n/6\rceil .$$
--
--   This rung is open. Shen's theorem gives it for $n\ge 2\cdot 6^2-3\cdot 6+1=55$; the remaining values of $n$ are not covered by any published argument.
-- source:
--   Open; the status is surveyed in B. D. Sullivan, A summary of results and problems related to the Caccetta–Häggkvist conjecture, 2006, https://arxiv.org/abs/math/0605646. Known for n ≥ 2·36 − 18 + 1 = 55 by J. Shen, On the girth of digraphs, Discrete Math. 211 (2000), https://doi.org/10.1016/s0012-365x(99)00323-4

import Definitions.Def_TenChallenges_Challenge_03

namespace TenChallenges
theorem challenge_03_r6 : statement_03 6 := by sorry
end TenChallenges
