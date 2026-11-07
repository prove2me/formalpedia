-- Prove2me | Theorems.Thm_TenChallenges_challenge_04_r5
-- name    : TenChallenges.challenge_04_r5
-- status  : Open
-- author  : @utkuokur
-- created : 2026-11-04T21:41:07.192297+00:00
-- url     : https://prove2.me/theorems/9c3d276f-8fe4-4585-845b-1cc49accaa84
-- title:
--   Sidorenko's inequality for sides of size at most $5$
-- statement:
--   **The rung $r=5$ of the scaled Sidorenko conjecture.** For every finite graph $H$ admitting a bipartition with at most five vertices on each side, and every finite graph $G$ with at least one vertex,
--
--   $$t(H,G)\ \ge\ t(K_2,G)^{\,e(H)}.$$
--
--   This rung is open; it contains $K_{5,5}$ minus a $10$-cycle.
-- source:
--   Open; the smallest open case $K_{5,5}\setminus C_{10}$ is discussed in D. Conlon, J. Lee, Sidorenko's conjecture for blow-ups, Discrete Analysis 2021:2, https://doi.org/10.19086/da.21472

import Definitions.Def_TenChallenges_Challenge_04

namespace TenChallenges
theorem challenge_04_r5 : statement_04 5 := by sorry
end TenChallenges
