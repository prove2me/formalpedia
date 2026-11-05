-- Prove2me | Theorems.Thm_TenChallenges_challenge_03_r1
-- name    : TenChallenges.challenge_03_r1
-- status  : Proved
-- author  : @utkuokur
-- created : 2026-11-04T21:33:39.821054+00:00
-- url     : https://prove2.me/theorems/e28a1eea-acd9-4d25-8189-dbf03a3ff643
-- title:
--   Caccetta–Häggkvist for $r = 1$
-- statement:
--   **The rung $r=1$ of the Caccetta–Häggkvist conjecture.** Every loopless digraph on $n\ge 1$ vertices in which every vertex has at least one out-neighbour contains a directed cycle of length at most $n$:
--
--   $$\delta^+(D)\ge 1 \implies D \text{ has a directed cycle of length } \ell \text{ with } 2\le\ell\le n .$$
-- source:
--   Exercise; e.g. J. Bang-Jensen, G. Gutin, Digraphs, 2nd ed., Proposition 1.4.2 (a digraph with minimum out-degree at least one contains a cycle), https://doi.org/10.1007/978-1-84800-998-1

import Definitions.Def_TenChallenges_Challenge_03

namespace TenChallenges
theorem challenge_03_r1 : statement_03 1 := by sorry
end TenChallenges
