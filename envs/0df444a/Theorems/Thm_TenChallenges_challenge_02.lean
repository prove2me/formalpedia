-- Prove2me | Theorems.Thm_TenChallenges_challenge_02
-- name    : TenChallenges.challenge_02
-- status  : Open
-- author  : @utkuokur
-- created : 2026-11-04T21:55:04.564415+00:00
-- url     : https://prove2.me/theorems/5d312de8-1259-46bb-9c28-0bfa44fc859c
-- title:
--   Rota's conjecture: finitely many excluded minors for every finite field
-- statement:
--   **Rota's conjecture**, in the scaled form of Challenge 2. For every natural number $r$ there is a natural number $B$ such that
--
--   $$\text{for every prime power } p^m\le r,\ \text{the class of } \mathrm{GF}(p^m)\text{-representable matroids has at most } B \text{ excluded minors up to isomorphism.}$$
--
--   Since only finitely many prime powers lie below any $r$, this is equivalent to: every finite field has only finitely many excluded minors up to isomorphism. Geelen, Gerards and Whittle announced a proof in 2014; the complete argument has not been published, and no part of it has been formalized.
--
--   **Formalization Note.** $S(r,B)$ is the definition `statement_02 r B`; excluded minors are counted via a finite set of representatives on the ground type $\mathbb N$.
-- source:
--   V. Bajpai, N. Bowler, J. Carmesin, U. Okur, 10 Scalable Challenges in Combinatorics, AI4Math @ CICM 2026, challenge 2 (full form); G.-C. Rota, Combinatorial theory, old and new, ICM 1970 (the conjecture); J. Geelen, B. Gerards, G. Whittle, Solving Rota's conjecture, Notices AMS 61 (2014), https://doi.org/10.1090/noti1139

import Definitions.Def_TenChallenges_Challenge_02

namespace TenChallenges
theorem challenge_02 : ∀ r : ℕ, ∃ B : ℕ, statement_02 r B := by sorry
end TenChallenges
