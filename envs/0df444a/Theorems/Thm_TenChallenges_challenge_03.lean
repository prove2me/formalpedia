-- Prove2me | Theorems.Thm_TenChallenges_challenge_03
-- name    : TenChallenges.challenge_03
-- status  : Open
-- author  : @utkuokur
-- created : 2026-11-04T21:33:23.695122+00:00
-- url     : https://prove2.me/theorems/9a3e7783-4a0b-4248-878a-56a024313059
-- title:
--   Caccetta–Häggkvist conjecture
-- statement:
--   **The Caccetta–Häggkvist conjecture.** For every $r\ge 1$, every loopless digraph on $n\ge 1$ vertices in which every vertex has out-degree at least $r$ contains a directed cycle of length at most $\lceil n/r\rceil$:
--
--   $$\forall r\ge 1\ \ \forall D:\ \delta^+(D)\ge r \implies \text{girth}(D)\le\lceil n/r\rceil .$$
--
--   The circulant digraph on $\mathbb Z/n$ with arcs $v\to v+1,\dots,v+r$ shows that the bound cannot be improved. The conjecture is proved for $r\le 5$ and open for $r\ge 6$.
--
--   **Formalization Note.** The statement is `∀ r, statement_03 r`, where `statement_03 r` unfolds to `CaccettaHaggkvistFor r`; the case $r=0$ is vacuous.
-- source:
--   L. Caccetta, R. Häggkvist, On minimal digraphs with given girth, Proc. 9th Southeastern Conf. (1978), Congr. Numer. 21, 181–187 (the conjecture); V. Bajpai, N. Bowler, J. Carmesin, U. Okur, 10 Scalable Challenges in Combinatorics, AI4Math @ CICM 2026, challenge 3 (full form)

import Definitions.Def_TenChallenges_Challenge_03

namespace TenChallenges
theorem challenge_03 : ∀ r : ℕ, statement_03 r := by sorry
end TenChallenges
