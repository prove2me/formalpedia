-- Prove2me | Theorems.Thm_TenChallenges_challenge_04_r22
-- name    : TenChallenges.challenge_04_r22
-- status  : Open
-- author  : @utkuokur
-- created : 2026-11-06T10:24:14.615541+00:00
-- url     : https://prove2.me/theorems/5651d6de-b4be-4e96-b758-ffda11d43653
-- title:
--   Sidorenko's inequality for sides of size at most $22$
-- statement:
--   **The rung $r=22$ of the scaled Sidorenko conjecture.** For every finite graph $H$ admitting a bipartition with at most $22$ vertices on each side, and every finite graph $G$ with at least one vertex,
--
--   $$t(H,G)\ \ge\ t(K_2,G)^{\,e(H)}.$$
--
--   OpenAI's 2026 counterexample, a bipartite $H$ with sides of size $13$ and $22$ and a finite host $G$ violating the inequality, refutes this rung if it stands; the expected outcome is a disproof.
-- source:
--   OpenAI, A counterexample to Sidorenko's conjecture, manuscript dated 23 September 2026, released 6 October 2026, https://github.com/openai/math/blob/main/lean/docs/161.md (Lean statement OAI.SidorenkoCounterexample.main: H the incidence graph of 22 triples on 13 points)

import Definitions.Def_TenChallenges_Challenge_04

namespace TenChallenges
theorem challenge_04_r22 : statement_04 22 := by sorry
end TenChallenges
