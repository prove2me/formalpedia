-- Prove2me | Theorems.Thm_TenChallenges_challenge_05
-- name    : TenChallenges.challenge_05
-- status  : Open
-- author  : @utkuokur
-- created : 2026-11-04T21:29:21.391555+00:00
-- url     : https://prove2.me/theorems/d8897103-e1bb-4fc7-a699-552b2894c612
-- title:
--   Erdős–Hajnal conjecture for all paths
-- statement:
--   **The Erdős–Hajnal conjecture for all paths.** For every $r\in\mathbb N$ there is a constant $c_r>0$ such that every finite graph with no induced path on $r$ vertices has a clique or an independent set of size at least $n^{c_r}$, where $n$ is its number of vertices:
--
--   $$\forall r\ \ \exists c_r>0\ \ \forall G\ P_r\text{-free}:\quad \max(\omega(G),\alpha(G))\ \ge\ n^{c_r}.$$
--
--   Known for $r\le 5$; open for $r\ge 6$.
--
--   **Formalization Note.** The statement is `∀ r, statement_05 r`, where `statement_05 r` is the Erdős–Hajnal property for `pathGraph r`.
-- source:
--   P. Erdős, A. Hajnal, Ramsey-type theorems, Discrete Appl. Math. 25 (1989), https://doi.org/10.1016/0166-218X(89)90045-0 (the conjecture, restricted to paths); V. Bajpai, N. Bowler, J. Carmesin, U. Okur, 10 Scalable Challenges in Combinatorics, AI4Math @ CICM 2026, challenge 5 (full form)

import Definitions.Def_TenChallenges_Challenge_05

namespace TenChallenges
theorem challenge_05 : ∀ r : ℕ, statement_05 r := by sorry
end TenChallenges
