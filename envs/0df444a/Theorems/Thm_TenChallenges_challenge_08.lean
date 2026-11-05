-- Prove2me | Theorems.Thm_TenChallenges_challenge_08
-- name    : TenChallenges.challenge_08
-- status  : Open
-- author  : @utkuokur
-- created : 2026-11-04T21:16:14.248668+00:00
-- url     : https://prove2.me/theorems/a66bfb27-5711-4a97-b85a-e6d1f84531b2
-- title:
--   Ryser's conjecture
-- statement:
--   **Ryser's conjecture.** For every $r\ge 2$, every $r$-partite $r$-uniform finite hypergraph $\mathcal H$ satisfies
--
--   $$\tau(\mathcal H)\ \le\ (r-1)\,\nu(\mathcal H),$$
--
--   where $\tau(\mathcal H)$ is the least size of a set of vertices meeting every edge and $\nu(\mathcal H)$ the largest number of pairwise disjoint edges. For $r=2$ this is Kőnig's theorem, for $r=3$ Aharoni's theorem; for $r\ge 4$ the conjecture is open.
--
--   **Formalization Note.** The statement is `∀ r, statement_08.{u} r`; the values $r\le 1$ are vacuous by the guard $2\le r$.
-- source:
--   Ryser's conjecture, as stated in R. Aharoni, Ryser's conjecture for tripartite 3-graphs, Combinatorica 21 (2001), 1–4, https://doi.org/10.1007/s004930170001; scaled form in V. Bajpai, N. Bowler, J. Carmesin, U. Okur, 10 Scalable Challenges in Combinatorics, AI4Math @ CICM 2026, challenge 8

import Definitions.Def_TenChallenges_Challenge_08
universe u

namespace TenChallenges
theorem challenge_08 : ∀ r : ℕ, statement_08.{u} r := by sorry
end TenChallenges
